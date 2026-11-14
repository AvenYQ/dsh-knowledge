/**
 * dsh-knowledge — Host half.
 *
 * 职责：数据源注册 → 扫描 → 切块 → SQLite/FTS5 索引 → 检索 → HTTP API。
 * 前端（client.js）通过 /knowledge/api/* 读取；Agent 通过 kb_search 工具读取。
 *
 * 只读设计：对源文件零写入。
 *
 * 0.2.0 起：每个数据源挂递归文件夹监听，文件新增/修改/删除后约 1.5 秒自动增量入库，
 * 不需要重启 DSH 或手动扫描；每 10 分钟的定时对账保留，作为兜底。
 *
 * 0.3.0 起：多词模糊检索（问句也能搜到）；问答接口 chat —— 先让模型拆关键词，
 * 按范围翻找，判断够不够（最多 3 轮），再流式写出带 [n] 角标的回答；话题存在 chats/ 下。
 */
import { promises as fsp, watch as fsWatch } from 'node:fs';
import { execFile } from 'node:child_process';
import { createHash } from 'node:crypto';
import { DatabaseSync } from 'node:sqlite';
import { homedir } from 'node:os';
import path from 'node:path';

export const inject = ['webServer'];

const PLUGIN = 'dsh-knowledge';
const VERSION = '0.3.0';
const DEFAULT_DATA_DIR = path.join(homedir(), '.dsh', 'knowledge');
const DB_FILE = 'kb.db';
const CONFIG_FILE = 'config.json';

const HOME = homedir();

export const DEFAULT_CONFIG = {
  dataDir: DEFAULT_DATA_DIR,
  chunk: { sizeLatin: 1500, sizeCjk: 560, overlapLatin: 200, overlapCjk: 80 },
  ignoreDirs: ['.git', 'node_modules', '.obsidian', '.trash', 'trash', 'tmp', '.DS_Store', '__pycache__', '.idea'],
  includeExt: ['.md', '.markdown', '.txt'],
  maxFilesPerSource: 5000,
  sources: [
    { id: 'work-vault', label: '工作知识库', path: path.join(HOME, 'Desktop', '工作知识库'), kind: 'vault', enabled: true },
    { id: 'work-project', label: '汽车开关工程', path: path.join(HOME, 'Desktop', '汽车开关工程'), kind: 'folder', enabled: true },
  ],
};

/* ─────────────────────────── 配置 ─────────────────────────── */

function expand(p) {
  if (typeof p !== 'string') return p;
  if (p === '~') return HOME;
  if (p.startsWith('~/')) return path.join(HOME, p.slice(2));
  return p;
}

async function loadConfig() {
  const file = path.join(DEFAULT_DATA_DIR, CONFIG_FILE);
  try {
    const raw = await fsp.readFile(file, 'utf8');
    const parsed = JSON.parse(raw);
    return { ...DEFAULT_CONFIG, ...parsed, chunk: { ...DEFAULT_CONFIG.chunk, ...(parsed.chunk || {}) } };
  } catch {
    return { ...DEFAULT_CONFIG };
  }
}

async function saveConfig(config) {
  const dir = expand(config.dataDir || DEFAULT_DATA_DIR);
  await fsp.mkdir(dir, { recursive: true });
  await fsp.writeFile(path.join(dir, CONFIG_FILE), JSON.stringify(config, null, 2), 'utf8');
}

/* ─────────────────────────── 切块 ─────────────────────────── */

function cjkRatio(text) {
  const head = text.slice(0, 20000);
  let cjk = 0;
  let latin = 0;
  for (const ch of head) {
    const c = ch.codePointAt(0);
    if ((c >= 0x3040 && c <= 0x30ff) || (c >= 0x3400 && c <= 0x9fff) || (c >= 0xac00 && c <= 0xd7af) || (c >= 0xf900 && c <= 0xfaff)) cjk += 1;
    else if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122)) latin += 1;
  }
  const t = cjk + latin;
  return t === 0 ? 0 : cjk / t;
}

function chunkParams(text, cfg) {
  const r = cjkRatio(text);
  const size = Math.round(cfg.sizeLatin - (cfg.sizeLatin - cfg.sizeCjk) * r);
  const overlap = Math.round(cfg.overlapLatin - (cfg.overlapLatin - cfg.overlapCjk) * r);
  return { size: Math.max(120, size), overlap: Math.max(20, Math.min(overlap, Math.floor(size / 2))) };
}

/** 切成"原子片段"：按句末标点 / 换行切开，保留分隔符。 */
function atomize(text) {
  const out = [];
  const re = /[^。！？；\n.!?;]+[。！？；\n.!?;]*/g;
  let m;
  let last = 0;
  while ((m = re.exec(text)) !== null) {
    if (m[0].length > 0) out.push({ text: m[0], start: m.index });
    last = re.lastIndex;
    if (re.lastIndex === m.index) re.lastIndex += 1;
  }
  if (last < text.length) out.push({ text: text.slice(last), start: last });
  if (out.length === 0 && text.length > 0) out.push({ text, start: 0 });
  return out;
}

/** 贪心装箱 + 重叠。返回 [{text,start}]。 */
function chunkText(text, size, overlap) {
  const atoms = atomize(text);
  const chunks = [];
  let i = 0;
  let guard = 0;
  while (i < atoms.length && guard < 100000) {
    guard += 1;
    let len = 0;
    let j = i;
    const parts = [];
    while (j < atoms.length && (parts.length === 0 || len + atoms[j].text.length <= size)) {
      parts.push(atoms[j]);
      len += atoms[j].text.length;
      j += 1;
    }
    // 单个原子超长（大表格/代码块）→ 硬切
    if (parts.length === 1 && parts[0].text.length > size * 2) {
      const a = parts[0];
      for (let k = 0; k < a.text.length; k += size) {
        chunks.push({ text: a.text.slice(k, k + size), start: a.start + k });
      }
      i = j;
      continue;
    }
    const body = parts.map((p) => p.text).join('').replace(/\s+$/, '');
    if (body.trim().length > 0) chunks.push({ text: body, start: parts[0].start });
    if (j >= atoms.length) break;
    let back = 0;
    let k = j;
    while (k > i && back < overlap) {
      k -= 1;
      back += atoms[k].text.length;
    }
    i = k > i ? k : j;
  }
  return chunks;
}

/** 计算每个 chunk 的最近标题与行号。 */
function locate(text, chunks) {
  const headings = [];
  const lines = text.split('\n');
  let offset = 0;
  for (const line of lines) {
    const m = /^(#{1,6})\s+(.*)$/.exec(line);
    if (m) headings.push({ start: offset, level: m[1].length, title: m[2].trim() });
    offset += line.length + 1;
  }
  // 前缀行号表（累计偏移）
  const lineStarts = [0];
  for (let idx = 0; idx < lines.length; idx += 1) lineStarts.push(lineStarts[idx] + lines[idx].length + 1);

  const lineOf = (pos) => {
    let lo = 0;
    let hi = lineStarts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (lineStarts[mid] <= pos) lo = mid;
      else hi = mid - 1;
    }
    return lo + 1;
  };

  return chunks.map((c) => {
    let header = '';
    for (const hd of headings) {
      if (hd.start <= c.start) header = hd.title;
      else break;
    }
    return { ...c, header, line: lineOf(c.start) };
  });
}

/* ─────────────────────────── 索引 ─────────────────────────── */

function openDb(dataDir) {
  const dir = expand(dataDir || DEFAULT_DATA_DIR);
  const db = new DatabaseSync(path.join(dir, DB_FILE));
  db.exec('pragma journal_mode = WAL');
  db.exec('pragma synchronous = NORMAL');
  db.exec(`create table if not exists sources (
    id text primary key, label text, path text, kind text, enabled integer, added_at text
  )`);
  db.exec(`create table if not exists docs (
    id text primary key, source_id text, path text, rel_path text, title text,
    hash text, bytes integer, mtime integer, lines integer, chunk_count integer,
    superseded integer default 0, updated_at text
  )`);
  db.exec(`create table if not exists chunks (
    rowid integer primary key, doc_id text, idx integer, text text, header text, line integer
  )`);
  db.exec(`create virtual table if not exists chunks_fts using fts5(text, header, tokenize='trigram')`);
  db.exec('create index if not exists docs_source on docs(source_id)');
  db.exec('create index if not exists chunks_doc on chunks(doc_id)');
  return db;
}

function sha256(text) {
  return createHash('sha256').update(text, 'utf8').digest('hex');
}

function ftsQuery(q) {
  const clean = q.replace(/["']/g, ' ').replace(/\s+/g, ' ').trim();
  if (!clean) return null;
  return `"${clean}"`;
}

function normalize(list) {
  if (list.length === 0) return list;
  const scores = list.map((x) => x.raw);
  const min = Math.min(...scores);
  const max = Math.max(...scores);
  const span = max - min;
  return list.map((x) => ({ ...x, norm: span === 0 ? 1 : (x.raw - min) / span }));
}

const W_FTS = 0.55;
const W_TITLE = 0.3;
const W_EXACT = 0.15;

function searchChunks(db, q, limit) {
  const query = (q || '').trim();
  if (!query) return [];
  const candidates = new Map();
  const add = (row, source, raw, extra) => {
    const key = row.rowid;
    const cur = candidates.get(key) || { row, sources: {}, raw: 0 };
    cur.sources[source] = Math.max(cur.sources[source] || 0, raw);
    if (extra) cur.extra = extra;
    candidates.set(key, cur);
  };

  // ① FTS5 trigram（≥3 字符有效）
  if (query.length >= 3) {
    const fq = ftsQuery(query);
    if (fq) {
      try {
        const rows = db
          .prepare(
            `select c.rowid as rowid, c.doc_id, c.idx, c.text, c.header, c.line, bm25(chunks_fts) as s
             from chunks_fts f join chunks c on c.rowid = f.rowid
             where chunks_fts match ? order by s limit ?`,
          )
          .all(fq, Math.max(limit * 6, 40));
        for (const r of rows) add(r, 'fts', -Number(r.s || 0));
      } catch {
        /* trigram 查询失败时走 LIKE */
      }
    }
  }

  // ② LIKE 兜底（中文 1–2 字必走这里）
  if (candidates.size === 0 || query.length < 3) {
    const like = `%${query.replace(/[%_]/g, '')}%`;
    const rows = db
      .prepare(
        `select c.rowid as rowid, c.doc_id, c.idx, c.text, c.header, c.line
         from chunks c where c.text like ? or c.header like ? limit ?`,
      )
      .all(like, like, Math.max(limit * 6, 40));
    for (const r of rows) add(r, 'like', 0.6);
  }

  // ③ 标题 / 路径路
  const titleRows = db
    .prepare(`select id, path, rel_path, title from docs where title like ? or rel_path like ? limit ?`)
    .all(`%${query}%`, `%${query}%`, 30);
  const titleHitDocs = new Set(titleRows.map((r) => r.id));
  if (titleHitDocs.size > 0) {
    const placeholders = [...titleHitDocs].map(() => '?').join(',');
    const rows = db
      .prepare(`select rowid, doc_id, idx, text, header, line from chunks where doc_id in (${placeholders}) limit ?`)
      .all(...titleHitDocs, Math.max(limit * 4, 20));
    for (const r of rows) add(r, 'title', 0.8);
  }

  // ④ 归一化加权融合
  const list = [...candidates.values()];
  const perSource = {};
  for (const key of ['fts', 'like', 'title']) {
    perSource[key] = normalize(list.filter((c) => c.sources[key] !== undefined).map((c) => ({ ...c, raw: c.sources[key] })));
  }
  const normMap = new Map();
  for (const key of Object.keys(perSource)) {
    for (const item of perSource[key]) normMap.set(item.row.rowid, { ...(normMap.get(item.row.rowid) || {}), [key]: item.norm });
  }
  const scored = list.map((c) => {
    const n = normMap.get(c.row.rowid) || {};
    let score = W_FTS * (n.fts || 0) + W_TITLE * (n.title || 0);
    if (c.sources.like !== undefined) score = Math.max(score, W_FTS * 0.9);
    const exact = c.row.text.includes(query) || (c.row.header || '').includes(query);
    if (exact) score += W_EXACT;
    return { ...c.row, score };
  });

  // ⑤ 每文档最多 3 条
  const byDoc = new Map();
  for (const item of scored.sort((a, b) => b.score - a.score)) {
    const arr = byDoc.get(item.doc_id) || [];
    if (arr.length < 3) arr.push(item);
    byDoc.set(item.doc_id, arr);
  }
  const flat = [...byDoc.values()].flat().sort((a, b) => b.score - a.score).slice(0, limit);

  const docIds = [...new Set(flat.map((x) => x.doc_id))];
  const docs = new Map();
  if (docIds.length > 0) {
    const rows = db
      .prepare(`select id, path, rel_path, title, source_id, superseded from docs where id in (${docIds.map(() => '?').join(',')})`)
      .all(...docIds);
    for (const r of rows) docs.set(r.id, r);
  }
  return flat.map((x) => {
    const d = docs.get(x.doc_id) || {};
    return {
      path: d.path || '',
      relPath: d.rel_path || '',
      title: d.title || '',
      sourceId: d.source_id || '',
      superseded: !!d.superseded,
      line: x.line,
      header: x.header || '',
      text: x.text,
      score: Number(x.score.toFixed(4)),
    };
  });
}

/* ─────────────────────────── 扫描 ─────────────────────────── */

const state = {
  scanning: false,
  progress: '',
  lastScanAt: null,
  lastScanResult: null,
  lastError: null,
};

async function walkFiles(root, config) {
  const out = [];
  const stack = [root];
  const ignore = new Set(config.ignoreDirs || []);
  const exts = new Set((config.includeExt || []).map((x) => x.toLowerCase()));
  while (stack.length > 0) {
    const dir = stack.pop();
    let entries;
    try {
      entries = await fsp.readdir(dir, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const entry of entries) {
      const full = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        if (ignore.has(entry.name)) continue;
        if (entry.name.startsWith('.') && entry.name !== '.') continue;
        stack.push(full);
      } else if (entry.isFile()) {
        const ext = path.extname(entry.name).toLowerCase();
        if (!exts.has(ext)) continue;
        out.push(full);
        if (out.length >= (config.maxFilesPerSource || 5000)) return out;
      }
    }
  }
  return out;
}

function isSupersededPath(rel) {
  return /90_历史版本|_旧版_|作废|trash\//i.test(rel);
}

async function indexFile(db, config, source, absPath, opts = {}) {
  const raw = await fsp.readFile(absPath, 'utf8');
  const text = raw.replace(/\r\n/g, '\n');
  const hash = sha256(text);
  const rel = path.relative(expand(source.path), absPath);
  const stat = await fsp.stat(absPath);

  const existing = db.prepare('select id, hash from docs where path = ?').get(absPath);
  if (existing && existing.hash === hash) {
    return { changed: false, chunks: 0 };
  }

  // 标题：跳过开头的 front matter（--- … ---）；front matter 里有 title 就用它，否则用正文第一行，都没有就用文件名
  let body = text;
  let fmTitle = '';
  const fm = /^---\n([\s\S]*?)\n---\s*\n?/.exec(text);
  if (fm) {
    body = text.slice(fm[0].length);
    const t = /^(?:title|name):\s*["']?(.+?)["']?\s*$/m.exec(fm[1]);
    if (t) fmTitle = t[1];
  }
  const firstLine = body.split('\n').find((l) => l.trim().length > 0) || '';
  const title = (fmTitle || firstLine.replace(/^#+\s*/, '').trim() || path.basename(rel).replace(/\.[^.]+$/, '')).slice(0, 120);
  const { size, overlap } = chunkParams(text, config.chunk || DEFAULT_CONFIG.chunk);
  const rawChunks = chunkText(text, size, overlap);
  const chunks = locate(text, rawChunks);
  const docId = existing ? existing.id : sha256(absPath).slice(0, 24);
  const lines = text.split('\n').length;
  const superseded = isSupersededPath(rel) ? 1 : 0;

  // 整篇替换放在一个事务里：要么全换成新内容，要么保持旧内容，不会留下半截。
  db.exec('begin');
  try {
    // 0.2.0 修复：旧版只删 chunks、不删 chunks_fts，重新入库时 rowid 复用会撞车，文件被记成「已入库」却只剩半截。
    db.prepare('delete from chunks_fts where rowid in (select rowid from chunks where doc_id = ?)').run(docId);
    db.prepare('delete from chunks where doc_id = ?').run(docId);
    db.prepare(
      `insert into docs (id, source_id, path, rel_path, title, hash, bytes, mtime, lines, chunk_count, superseded, updated_at)
       values (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
       on conflict(id) do update set source_id=excluded.source_id, path=excluded.path, rel_path=excluded.rel_path,
         title=excluded.title, hash=excluded.hash, bytes=excluded.bytes, mtime=excluded.mtime, lines=excluded.lines,
         chunk_count=excluded.chunk_count, superseded=excluded.superseded, updated_at=excluded.updated_at`,
    ).run(docId, source.id, absPath, rel, title, hash, stat.size, Math.round(stat.mtimeMs), lines, chunks.length, superseded, new Date().toISOString());

    const insChunk = db.prepare('insert into chunks (doc_id, idx, text, header, line) values (?, ?, ?, ?, ?)');
    const insFts = db.prepare('insert into chunks_fts (rowid, text, header) values (?, ?, ?)');
    for (let i = 0; i < chunks.length; i += 1) {
      const info = insChunk.run(docId, i, chunks[i].text, chunks[i].header || '', chunks[i].line);
      insFts.run(info.lastInsertRowid, chunks[i].text, chunks[i].header || '');
    }
    db.exec('commit');
    if (opts.announce) {
      state.ingestSeq = (state.ingestSeq || 0) + 1;
      state.ingest = { seq: state.ingestSeq, docId, title, sourceId: source.id, rel, at: new Date().toISOString(), isNew: !existing };
    }
  } catch (error) {
    try {
      db.exec('rollback');
    } catch {
      /* ignore */
    }
    throw error;
  }
  return { changed: true, chunks: chunks.length };
}

/** 从索引里移除一篇文档（含全文索引）。 */
function removeDoc(db, docId) {
  db.prepare('delete from chunks_fts where rowid in (select rowid from chunks where doc_id = ?)').run(docId);
  db.prepare('delete from chunks where doc_id = ?').run(docId);
  db.prepare('delete from docs where id = ?').run(docId);
}

/** 启动自检：清掉旧版残留的全文索引孤儿行、补齐缺失行；片段数对不上的文档清指纹，下次扫描整篇重建。 */
function repairIndex(db) {
  const orphan = db.prepare('delete from chunks_fts where rowid not in (select rowid from chunks)').run().changes;
  const missing = db.prepare('select rowid, text, header from chunks where rowid not in (select rowid from chunks_fts)').all();
  const insFts = db.prepare('insert into chunks_fts (rowid, text, header) values (?, ?, ?)');
  for (const r of missing) insFts.run(r.rowid, r.text, r.header || '');
  const broken = db
    .prepare(`update docs set hash = '' where chunk_count != (select count(*) from chunks c where c.doc_id = docs.id) or title = '---'`)
    .run().changes;
  return { orphan: Number(orphan), missing: missing.length, broken: Number(broken) };
}

/** 扫描、监听、接口里的写库操作排队执行，互不打断。 */
let lockChain = Promise.resolve();
function withLock(fn) {
  const run = lockChain.then(fn);
  lockChain = run.catch(() => {});
  return run;
}

async function pathExists(p) {
  try {
    await fsp.access(p);
    return true;
  } catch {
    return false;
  }
}

/** 扫描单个数据源：增量入库 + 删除已消失的文件。 */
async function scanSource(db, config, source) {
  const root = expand(source.path);
  db.prepare(
    `insert into sources (id, label, path, kind, enabled, added_at) values (?, ?, ?, ?, 1, ?)
     on conflict(id) do update set label=excluded.label, path=excluded.path, kind=excluded.kind, enabled=1`,
  ).run(source.id, source.label || source.id, root, source.kind || 'folder', new Date().toISOString());

  const base = { id: source.id, label: source.label || source.id, files: 0, changed: 0, removed: 0, chunks: 0 };
  // 根目录暂时不在（外接盘没插、文件夹被移走）时不动索引，免得一次误判清空整个源。
  if (!(await pathExists(root))) return { ...base, missing: true };

  const files = await walkFiles(root, config);
  const seen = new Set();
  let changed = 0;
  let chunks = 0;
  state.scanProg = { id: source.id, done: 0, total: files.length };
  for (const file of files) {
    seen.add(file);
    state.scanProg.done += 1;
    try {
      const r = await indexFile(db, config, source, file);
      if (r.changed) {
        changed += 1;
        chunks += r.chunks;
      }
    } catch (error) {
      // 单个文件失败不影响整体
    }
  }
  const known = db.prepare('select id, path from docs where source_id = ?').all(source.id);
  let removed = 0;
  for (const row of known) {
    if (!seen.has(row.path)) {
      removeDoc(db, row.id);
      removed += 1;
    }
  }
  state.scanProg = null;
  return { ...base, files: files.length, changed, removed, chunks };
}

async function scanAll(db, config) {
  if (state.scanning) return state.lastScanResult;
  state.scanning = true;
  state.lastError = null;
  const result = { scanned: 0, changed: 0, removed: 0, chunks: 0, sources: [] };
  try {
    await withLock(async () => {
      for (const source of config.sources || []) {
        if (!source.enabled) continue;
        state.progress = `扫描 ${source.label || source.id}`;
        const r = await scanSource(db, config, source);
        result.scanned += r.files;
        result.changed += r.changed;
        result.chunks += r.chunks;
        result.removed += r.removed;
        result.sources.push(r);
      }
    });
    state.lastScanAt = new Date().toISOString();
    state.lastScanResult = result;
    return result;
  } catch (error) {
    state.lastError = String((error && error.message) || error);
    return result;
  } finally {
    state.scanning = false;
    state.progress = '';
  }
}

/* ─────────────────────────── 监听 ─────────────────────────── */

const WATCH_DEBOUNCE_MS = 1500;
const WATCH_RETRY_MS = 30 * 1000;

const watchState = { sources: {}, lastChangeAt: null, lastBatch: null };

/**
 * 对每个启用的数据源挂一个递归 fs.watch。变化攒 1.5 秒后一次处理：
 * 文件还在 → 增量入库（hash 未变则跳过）；文件没了 → 从索引删除；
 * 无后缀的路径（多半是文件夹改名/删除）或系统没给文件名 → 整个源重扫一遍。
 */
function createWatcher(db, config) {
  const entries = new Map(); // sourceId -> { root, watcher, retry }
  const pending = new Map(); // 绝对路径 -> sourceId
  const rescan = new Set(); // 需要整源重扫的 sourceId
  let timer = null;
  let closed = false;

  const sourceById = (id) => (config.sources || []).find((s) => s.id === id && s.enabled);

  function classify(rel) {
    const ignore = new Set(config.ignoreDirs || []);
    const parts = rel.split(/[\\/]/).filter(Boolean);
    if (parts.length === 0) return 'dir';
    for (const seg of parts) {
      if (ignore.has(seg) || seg.startsWith('.')) return 'skip';
    }
    const ext = path.extname(parts[parts.length - 1]).toLowerCase();
    const exts = new Set((config.includeExt || []).map((x) => x.toLowerCase()));
    if (exts.has(ext)) return 'file';
    if (!ext) return 'dir';
    return 'skip';
  }

  function schedule() {
    if (closed) return;
    if (timer) clearTimeout(timer);
    timer = setTimeout(() => {
      timer = null;
      flush().catch(() => {});
    }, WATCH_DEBOUNCE_MS);
  }

  function onEvent(id, root, filename) {
    if (closed) return;
    if (!filename) {
      rescan.add(id);
      watchState.lastChangeAt = new Date().toISOString();
      schedule();
      return;
    }
    const rel = String(filename);
    const kind = classify(rel);
    if (kind === 'skip') return;
    watchState.lastChangeAt = new Date().toISOString();
    if (kind === 'dir') rescan.add(id);
    else pending.set(path.join(root, rel), id);
    schedule();
  }

  async function flush() {
    if (pending.size === 0 && rescan.size === 0) return;
    const files = [...pending];
    pending.clear();
    const sources = [...rescan];
    rescan.clear();
    await withLock(async () => {
      if (closed) return;
      const batch = { at: new Date().toISOString(), indexed: 0, removed: 0, rescanned: 0 };
      for (const [abs, id] of files) {
        if (sources.includes(id)) continue; // 整源重扫会覆盖
        const source = sourceById(id);
        if (!source) continue;
        let st = null;
        try {
          st = await fsp.stat(abs);
        } catch {
          st = null;
        }
        if (st && st.isFile()) {
          try {
            const r = await indexFile(db, config, source, abs, { announce: true });
            if (r.changed) batch.indexed += 1;
          } catch {
            /* 读不到（正在写、权限）就留给下次变化或定时对账 */
          }
        } else if (!st) {
          const row = db.prepare('select id from docs where path = ?').get(abs);
          if (row) {
            removeDoc(db, row.id);
            batch.removed += 1;
          }
        }
      }
      for (const id of sources) {
        const source = sourceById(id);
        if (!source) continue;
        try {
          const r = await scanSource(db, config, source);
          batch.indexed += r.changed;
          batch.removed += r.removed;
          batch.rescanned += 1;
        } catch {
          /* ignore */
        }
      }
      watchState.lastBatch = batch;
    });
  }

  function open(source) {
    const root = expand(source.path);
    const entry = { root, watcher: null, retry: null };
    entries.set(source.id, entry);
    try {
      entry.watcher = fsWatch(root, { recursive: true, persistent: false }, (_type, filename) => onEvent(source.id, root, filename));
      entry.watcher.on('error', (error) => fail(source.id, error));
      watchState.sources[source.id] = { watching: true, error: null };
    } catch (error) {
      fail(source.id, error);
    }
  }

  function fail(id, error) {
    const entry = entries.get(id);
    if (!entry) return;
    try {
      entry.watcher?.close();
    } catch {
      /* ignore */
    }
    entry.watcher = null;
    watchState.sources[id] = { watching: false, error: String((error && error.message) || error) };
    if (closed || entry.retry) return;
    entry.retry = setTimeout(() => {
      entry.retry = null;
      if (closed || entries.get(id) !== entry) return;
      entries.delete(id);
      const source = sourceById(id);
      if (!source) return;
      open(source);
      if (entries.get(id)?.watcher) {
        rescan.add(id); // 补上断开期间漏掉的变化
        schedule();
      }
    }, WATCH_RETRY_MS);
  }

  function close(id) {
    const entry = entries.get(id);
    if (!entry) return;
    if (entry.retry) clearTimeout(entry.retry);
    try {
      entry.watcher?.close();
    } catch {
      /* ignore */
    }
    entries.delete(id);
    delete watchState.sources[id];
  }

  /** 按当前 config.sources 开/关监听；路径变了的会重挂。 */
  function sync() {
    if (closed) return;
    const want = new Map((config.sources || []).filter((s) => s.enabled).map((s) => [s.id, expand(s.path)]));
    for (const [id, entry] of [...entries]) {
      if (!want.has(id) || want.get(id) !== entry.root) close(id);
    }
    for (const source of config.sources || []) {
      if (source.enabled && !entries.has(source.id)) open(source);
    }
  }

  function dispose() {
    closed = true;
    if (timer) clearTimeout(timer);
    timer = null;
    for (const id of [...entries.keys()]) close(id);
  }

  return { sync, dispose, flush };
}

/* ─────────────────────────── 多词模糊检索（0.3.0） ─────────────────────────── */

// 问句里的虚词：去掉后剩下的才是要找的东西。只去多字虚词和少数语气字，单字实词（会、要、在…）不能乱删，会把「会议」「要求」拆坏。
const STOP_MULTI = /(什么|怎么样|怎么|怎样|如何|为什么|为啥|哪些|哪个|哪里|哪儿|是不是|是否|有没有|可不可以|可以|能不能|一下|关于|还有|以及|我们|你们|他们|这个|那个|这些|那些|之前|上次|最后|到底|请问|告诉我|帮我|给我|讲了|说了|提到|一般|大概|大约)/g;
const STOP_ONE = /[的了吗呢吧啊呀么嘛哦]/g;

/** 把查询拆成：整词（用来加分）+ 二字片段（用来召回和打分）。 */
function queryTerms(q) {
  const text = String(q || '').toLowerCase().slice(0, 200);
  const terms = new Set();
  const bigrams = new Set();
  const segs = text.match(/[㐀-鿿぀-ヿ]+|[a-z0-9][a-z0-9._+#-]*/g) || [];
  for (const seg of segs) {
    if (/^[a-z0-9]/.test(seg)) {
      if (seg.length >= 2) terms.add(seg);
      continue;
    }
    const pieces = seg.replace(STOP_MULTI, ' ').replace(STOP_ONE, ' ').split(' ').filter(Boolean);
    for (const p of pieces) {
      if (p.length === 1) continue;
      terms.add(p);
      for (let i = 0; i + 2 <= p.length; i += 1) bigrams.add(p.slice(i, i + 2));
    }
  }
  // 只剩一个字（刚开始打字）：就按这个字找
  if (terms.size === 0) {
    const one = (text.match(/[㐀-鿿]/) || [])[0];
    if (one) terms.add(one);
  }
  return { terms: [...terms].slice(0, 8), bigrams: [...bigrams].slice(0, 16) };
}

/**
 * 多词模糊检索：先按片段召回候选，再在内存里打分。
 * 分数 = 命中的片段比例 + 整词命中加分 + 标题命中加分；作废的版本打六折。每篇最多取 perDoc 段。
 */
function searchSmart(db, q, limit = 8, opts = {}) {
  const { terms, bigrams } = queryTerms(q);
  const keys = bigrams.length ? bigrams : terms;
  if (keys.length === 0) return { results: [], terms: [] };
  const scope = Array.isArray(opts.scope) && opts.scope.length ? opts.scope.map(String) : null;
  const perDoc = opts.perDoc || 2;

  const likes = keys.map(() => '(c.text like ? or c.header like ? or d.title like ?)').join(' or ');
  const args = [];
  for (const k of keys) {
    const p = `%${k.replace(/[%_]/g, '')}%`;
    args.push(p, p, p);
  }
  let where = `(${likes})`;
  if (scope) {
    where += ` and d.source_id in (${scope.map(() => '?').join(',')})`;
    args.push(...scope);
  }
  const rows = db
    .prepare(
      `select c.rowid as rowid, c.doc_id, c.idx, c.text, c.header, c.line,
              d.path, d.rel_path, d.title, d.source_id, d.superseded, d.mtime
       from chunks c join docs d on d.id = c.doc_id where ${where} limit 1500`,
    )
    .all(...args);

  const scored = [];
  for (const r of rows) {
    const hay = `${r.header || ''}\n${r.text}`.toLowerCase();
    const title = String(r.title || '').toLowerCase();
    let hit = 0;
    for (const k of keys) {
      if (hay.includes(k)) hit += 1;
      else if (title.includes(k)) hit += 0.7;
    }
    let score = hit / keys.length;
    for (const t of terms) {
      if (t.length < 2) continue;
      if (hay.includes(t)) score += 0.6 * Math.min(1, t.length / 4);
      if (title.includes(t)) score += 0.5 * Math.min(1, t.length / 4);
    }
    if (r.superseded) score *= 0.6;
    // 片段多的长问句：只命中一两个零碎片段的不算
    if (score > (keys.length >= 4 ? 0.2 : 0)) scored.push({ ...r, score });
  }
  scored.sort((a, b) => b.score - a.score || (b.mtime || 0) - (a.mtime || 0));

  const per = new Map();
  const out = [];
  for (const r of scored) {
    const n = per.get(r.doc_id) || 0;
    if (n >= perDoc) continue;
    per.set(r.doc_id, n + 1);
    out.push({
      docId: r.doc_id,
      idx: r.idx,
      path: r.path,
      relPath: r.rel_path,
      title: r.title,
      sourceId: r.source_id,
      superseded: !!r.superseded,
      line: r.line,
      header: r.header || '',
      text: r.text,
      score: Number(r.score.toFixed(4)),
    });
    if (out.length >= limit) break;
  }
  return { results: out, terms: [...new Set([...terms, ...bigrams])] };
}

/* ─────────────────────────── 数据源的样子（颜色、符号） ─────────────────────────── */

const SRC_COLORS = ['#7B61FF', '#2F80ED', '#FF8A3D', '#20B486', '#E5484D', '#D6409F', '#0EA5A4', '#B7791F'];

function sourceLook(source, index) {
  const p = String(source.path || '');
  let sym = 'dot';
  let kindLabel = source.kind === 'vault' ? 'Obsidian 库' : '文件夹';
  if (source.kind === 'vault') sym = 'note';
  else if (/拾穗|glean/i.test(p)) {
    sym = 'mark';
    kindLabel = '收藏';
  } else if (/会议|meeting/i.test(p)) sym = 'people';
  else if (/工程|项目|project/i.test(p)) sym = 'gear';
  else if (/读书|书|book|read/i.test(p)) sym = 'book';
  else if (/download/i.test(p)) sym = 'down';
  else sym = ['box', 'book', 'dot'][index % 3];
  return {
    color: source.color || SRC_COLORS[index % SRC_COLORS.length],
    sym: source.sym || sym,
    kindLabel: source.kindLabel || kindLabel,
  };
}

function prettyPath(p) {
  const s = String(p || '');
  return s.startsWith(HOME + path.sep) ? '~' + s.slice(HOME.length) : s;
}

async function sourcesView(db, config) {
  const counts = new Map(
    db
      .prepare('select source_id, count(*) d, coalesce(sum(chunk_count),0) c, coalesce(sum(bytes),0) b from docs group by source_id')
      .all()
      .map((r) => [r.source_id, r]),
  );
  const list = [];
  const sources = (config.sources || []).filter((s) => s.enabled);
  for (let i = 0; i < sources.length; i += 1) {
    const s = sources[i];
    const n = counts.get(s.id) || { d: 0, c: 0, b: 0 };
    const look = sourceLook(s, i);
    const w = watchState.sources[s.id];
    list.push({
      id: s.id,
      label: s.label || s.id,
      kind: s.kind || 'folder',
      kindLabel: look.kindLabel,
      path: expand(s.path),
      pathLabel: prettyPath(expand(s.path)),
      color: look.color,
      sym: look.sym,
      docs: Number(n.d),
      chunks: Number(n.c),
      bytes: Number(n.b),
      watching: !!(w && w.watching),
      watchError: (w && w.error) || null,
      missing: !(await pathExists(expand(s.path))),
    });
  }
  return list;
}

/** 文档列表：浏览页的纸张。first 是正文前几行，用来画缩略图。 */
function docsOf(db, where, args, limit) {
  const rows = db
    .prepare(
      `select d.id, d.source_id, d.rel_path, d.title, d.mtime, d.updated_at, d.superseded, d.bytes, d.lines,
              (select text from chunks c where c.doc_id = d.id order by idx limit 1) as first
       from docs d ${where} order by d.mtime desc limit ?`,
    )
    .all(...args, limit);
  return rows.map((r) => ({
    id: r.id,
    sourceId: r.source_id,
    rel: r.rel_path,
    title: r.title,
    mtime: r.mtime,
    superseded: !!r.superseded,
    bytes: r.bytes,
    lines: r.lines,
    preview: previewLines(r.first || '', r.title),
  }));
}

function previewLines(text, title) {
  const out = [];
  for (const raw of String(text).split('\n')) {
    const l = raw
      .replace(/^#+\s*/, '')
      .replace(/^[-*+>]\s+/, '')
      .replace(/[*_`]/g, '')
      .replace(/\[\[([^\]|]+)(\|[^\]]+)?\]\]/g, '$1')
      .trim();
    if (!l || l === title || /^---$/.test(l) || /^\w+:\s/.test(l)) continue;
    out.push(l.slice(0, 90));
    if (out.length >= 4) break;
  }
  return out;
}

/* ─────────────────────────── 本机小动作：选文件夹、在 Finder 中显示 ─────────────────────────── */

function run(cmd, args, timeout = 120000) {
  return new Promise((resolve) => {
    execFile(cmd, args, { timeout }, (error, stdout, stderr) => resolve({ error, stdout: String(stdout || ''), stderr: String(stderr || '') }));
  });
}

async function pickFolder() {
  if (process.platform !== 'darwin') return { ok: false, error: '只支持 macOS' };
  const r = await run('osascript', ['-e', 'activate', '-e', 'POSIX path of (choose folder with prompt "选择要加入知识库的文件夹")']);
  if (r.error) {
    if (/-128|User canceled|用户已取消/i.test(r.stderr + String(r.error.message))) return { ok: true, cancelled: true };
    return { ok: false, error: (r.stderr || r.error.message).trim() };
  }
  const p = r.stdout.trim().replace(/\/$/, '');
  return p ? { ok: true, path: p } : { ok: true, cancelled: true };
}

async function revealPath(p) {
  if (process.platform !== 'darwin') return { ok: false, error: '只支持 macOS' };
  const r = await run('open', ['-R', p], 10000);
  return r.error ? { ok: false, error: (r.stderr || r.error.message).trim() } : { ok: true };
}

/* ─────────────────────────── 问答（0.3.0） ─────────────────────────── */

const CHAT_DIR = path.join(DEFAULT_DATA_DIR, 'chats');
const MAX_ROUNDS = 3;

async function listThreads() {
  let names = [];
  try {
    names = (await fsp.readdir(CHAT_DIR)).filter((n) => n.endsWith('.json'));
  } catch {
    return [];
  }
  const out = [];
  for (const n of names) {
    try {
      const t = JSON.parse(await fsp.readFile(path.join(CHAT_DIR, n), 'utf8'));
      out.push({ id: t.id, title: t.title, t: t.t, turns: (t.turns || []).length });
    } catch {
      /* 坏文件跳过 */
    }
  }
  return out.sort((a, b) => b.t - a.t).slice(0, 60);
}

const safeId = (id) => /^[a-z0-9-]{6,40}$/i.test(String(id || ''));

async function loadThread(id) {
  if (!safeId(id)) return null;
  try {
    return JSON.parse(await fsp.readFile(path.join(CHAT_DIR, `${id}.json`), 'utf8'));
  } catch {
    return null;
  }
}

async function saveThread(th) {
  await fsp.mkdir(CHAT_DIR, { recursive: true });
  const file = path.join(CHAT_DIR, `${th.id}.json`);
  await fsp.writeFile(`${file}.tmp`, JSON.stringify(th, null, 2), 'utf8');
  await fsp.rename(`${file}.tmp`, file);
}

async function deleteThread(id) {
  if (!safeId(id)) return;
  await fsp.rm(path.join(CHAT_DIR, `${id}.json`), { force: true });
}

function newThreadId() {
  return `${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`;
}

/** 从模型回复里抠出 JSON。 */
function pickJSON(text) {
  const t = String(text || '').replace(/```(?:json)?/gi, '');
  const a = t.indexOf('{');
  const b = t.lastIndexOf('}');
  if (a < 0 || b <= a) return null;
  try {
    return JSON.parse(t.slice(a, b + 1));
  } catch {
    return null;
  }
}

/** DSH 默认模型；helper=true 时同一家里有更快的非推理模型就用它，并关掉思考。 */
async function resolveRoute(ctx, llm, helper) {
  const sel = ctx.get?.('agentDefaultModel')?.currentSelection?.();
  let provider = sel?.provider;
  let model = sel?.model;
  if (!provider) provider = llm.listProviders?.()[0]?.id;
  if (!provider) throw new Error('DSH 里还没有可用的模型，请先在设置里添加');
  if (helper || !model) {
    try {
      const models = await llm.listModels(provider);
      const fast = helper && models.find((m) => /flash|chat|lite|mini|turbo|v3/i.test(m.id) && !/reason|r1|think|pro/i.test(m.id));
      if (fast) model = fast.id;
      if (!model) model = models[0]?.id;
    } catch {
      /* 列不出来就用默认 */
    }
  }
  if (!model) throw new Error('DSH 里还没有可用的模型，请先在设置里添加');
  let effort;
  if (helper) {
    const info = await llm.resolveModelInfo?.(provider, model).catch(() => undefined);
    const efforts = info?.reasoning?.efforts ?? [];
    effort = efforts.some((e) => e.id === 'off') ? 'off' : efforts.at(0)?.id;
  }
  return { provider, model, effort };
}

async function* llmStream(llm, route, system, messages, signal, maxTokens, sessionId) {
  let finish;
  for await (const chunk of llm.stream({
    provider: route.provider,
    model: route.model,
    ...(route.effort === undefined ? {} : { reasoningEffort: route.effort }),
    // 有的服务商（如 OpenCode）要求带会话标识，否则 400；每个话题一个固定标识
    ...(sessionId ? { sessionId } : {}),
    system,
    messages,
    maxTokens,
    signal,
  })) {
    if (chunk?.type === 'text-delta' && typeof chunk.text === 'string') yield chunk.text;
    else if (chunk?.type === 'finish') finish = chunk.reason;
  }
  if (finish && finish.kind === 'error') throw new Error(finish.failure?.message || '模型调用失败');
  if (finish && finish.kind === 'aborted') {
    const e = new Error('aborted');
    e.name = 'AbortError';
    throw e;
  }
}

async function llmText(llm, route, system, user, signal, maxTokens = 600, sessionId) {
  let out = '';
  for await (const t of llmStream(llm, route, system, [{ role: 'user', content: [{ type: 'text', text: user }] }], signal, maxTokens, sessionId)) out += t;
  return out;
}

const PLAN_SYS = `你在帮用户查他自己的本地知识库（工作笔记、项目文档、会议纪要、收藏的帖子，中文为主）。
根据用户的问题（以及之前的对话）给出 2～3 条检索词，用来在知识库里做关键词检索。
要求：每条 2～5 个关键词，用空格分开；用文档里可能出现的原词、术语、项目名，不要整句，不要「怎么」「什么」这类虚词；几条之间换个角度，不要重复。
只输出 JSON：{"queries":["…","…"]}`;

const JUDGE_SYS = `你在帮用户查他自己的本地知识库。下面是用户的问题、已经用过的检索词，以及目前找到的资料摘要。
判断这些资料是否足够回答问题。足够，或者再找也不太可能找到，就输出 {"enough":true}；
不够，就换个说法给 1～2 条新的检索词（不能和用过的重复），输出 {"enough":false,"queries":["…"]}。只输出 JSON。`;

const ANSWER_SYS = `你是用户的知识库助手，帮他读懂他自己的资料。下面给出编号的资料片段，回答必须以这些资料为依据。
规则：
1. 每一句来自资料的结论后面用 [n] 标出处，n 是资料编号，可以连写 [1][3]。不要编造编号，不要标不存在的编号。
2. 资料里没有的内容不能当成资料写。确实需要补充一般经验时，单独起一段，这一段的第一行只写 ::common ，后面的内容都算一般经验，不标编号。
3. 资料里找不到答案，就直接说知识库里没有找到，再视情况用 ::common 补充。
4. 资料标了「已作废」的，以新版为准，并提醒用户那是旧版。
5. 用中文，先给结论，简洁。可以用 **加粗** 标出关键结论，可以分段，不要用标题、表格和代码块。`;

function refBlock(refs) {
  return refs
    .map((r) => `[${r.n}] 《${r.title}》（${r.sourceLabel || ''} / ${r.rel}，第 ${r.line} 行${r.header ? `，${r.header}` : ''}）${r.superseded ? '【已作废】' : ''}\n${String(r.text).slice(0, 900)}`)
    .join('\n\n');
}

function historyMessages(th) {
  const msgs = [];
  for (const tu of (th.turns || []).slice(-3)) {
    if (!tu.ans) continue;
    msgs.push({ role: 'user', content: [{ type: 'text', text: tu.q }] });
    msgs.push({ role: 'assistant', content: [{ type: 'text', text: tu.ans }] });
  }
  return msgs;
}

/**
 * 一次问答。emit(event) 把进度推给前端；返回时线程已存盘。
 * 事件：thread / step / stepdone / refs / writing / delta / done / error
 */
async function runChat({ ctx, db, config, body, emit, signal }) {
  const llm = ctx.get?.('llm') || ctx.llm;
  const q = String(body.q || '').trim().slice(0, 2000);
  if (!q) throw new Error('问题是空的');
  const scope = Array.isArray(body.scope) ? body.scope.map(String) : [];
  let th = body.threadId ? await loadThread(body.threadId) : null;
  if (!th) th = { id: newThreadId(), title: q.replace(/[？?。.!！\s]+$/, '').slice(0, 24), t: Date.now(), turns: [], refs: [] };
  emit({ t: 'thread', id: th.id, title: th.title });

  const labels = new Map((config.sources || []).map((s) => [s.id, s.label || s.id]));
  const tu = { q, steps: [], ans: '', model: '', at: Date.now(), scope };
  th.turns.push(tu);
  th.t = Date.now();

  const save = () => saveThread(th).catch(() => {});
  try {
    if (!llm || typeof llm.stream !== 'function') throw new Error('DSH 的模型接口不可用');
    const helper = await resolveRoute(ctx, llm, true);
    const sid = `dsh-knowledge-${th.id}`;
    const history = (th.turns.slice(0, -1) || []).slice(-2).map((x) => `问：${x.q}\n答：${String(x.ans || '').slice(0, 400)}`).join('\n\n');

    // ① 拆检索词
    let queries = [];
    let planError = null;
    try {
      const plan = pickJSON(await llmText(llm, helper, PLAN_SYS, `${history ? `之前的对话：\n${history}\n\n` : ''}用户的问题：${q}`, signal, 300, sid));
      queries = (plan?.queries || []).map((x) => String(x).trim()).filter(Boolean).slice(0, 3);
    } catch (error) {
      if (signal.aborted) throw error;
      planError = String(error?.message || error);
    }
    if (queries.length === 0) queries = [q];

    // ② 翻找，最多 3 轮
    const used = [];
    const turnRefs = [];
    const keyOf = (r) => `${r.docId}:${r.idx}`;
    for (let round = 0; round < MAX_ROUNDS && queries.length; round += 1) {
      if (signal.aborted) throw Object.assign(new Error('aborted'), { name: 'AbortError' });
      const step = { kw: queries.join(' · '), again: round > 0, n: 0 };
      tu.steps.push(step);
      emit({ t: 'step', i: tu.steps.length - 1, kw: step.kw, again: step.again });
      used.push(...queries);
      const fresh = [];
      let reused = 0;
      for (const qq of queries) {
        for (const r of searchSmart(db, qq, 6, { scope, perDoc: 2 }).results) {
          if (fresh.length >= 8) break;
          const k = keyOf(r);
          if (th.refs.some((x) => keyOf(x) === k) && !turnRefs.some((x) => keyOf(x) === k)) {
            // 之前的回合已经引用过：这回合也算上，编号沿用
            turnRefs.push(th.refs.find((x) => keyOf(x) === k));
            reused += 1;
            continue;
          }
          if (turnRefs.some((x) => keyOf(x) === k) || fresh.some((x) => keyOf(x) === k)) continue;
          const sig = String(r.text).replace(/\s+/g, '').slice(0, 160);
          if (th.refs.some((x) => String(x.text).replace(/\s+/g, '').slice(0, 160) === sig) || fresh.some((x) => String(x.text).replace(/\s+/g, '').slice(0, 160) === sig)) continue;
          fresh.push(r);
        }
      }
      const added = fresh.map((r) => {
        const ref = {
          n: th.refs.length + 1,
          docId: r.docId,
          idx: r.idx,
          title: r.title,
          sourceId: r.sourceId,
          sourceLabel: labels.get(r.sourceId) || '',
          rel: r.relPath,
          path: r.path,
          line: r.line,
          header: r.header,
          superseded: r.superseded,
          text: r.text.slice(0, 1200),
        };
        th.refs.push(ref);
        turnRefs.push(ref);
        return ref;
      });
      step.n = fresh.length + reused;
      emit({ t: 'refs', step: tu.steps.length - 1, refs: added.map(publicRef) });
      emit({ t: 'stepdone', i: tu.steps.length - 1, n: step.n });
      if (round === MAX_ROUNDS - 1 || turnRefs.length >= 14) break;

      // ③ 够不够
      const digest = turnRefs.map((r) => `[${r.n}] ${r.title}${r.header ? ` · ${r.header}` : ''}：${String(r.text).replace(/\s+/g, ' ').slice(0, 140)}`).join('\n') || '（还没有找到任何资料）';
      let judge = null;
      try {
        judge = pickJSON(await llmText(llm, helper, JUDGE_SYS, `问题：${q}\n用过的检索词：${used.join('；')}\n找到的资料：\n${digest}`, signal, 200, sid));
      } catch (error) {
        if (signal.aborted) throw error;
      }
      if (!judge || judge.enough !== false) break;
      queries = (judge.queries || []).map((x) => String(x).trim()).filter((x) => x && !used.includes(x)).slice(0, 2);
    }

    // ④ 写回答
    emit({ t: 'writing' });
    const answerRoute = await resolveRoute(ctx, llm, false);
    tu.model = answerRoute.model;
    const shown = [...new Map([...th.refs.filter((r) => !turnRefs.includes(r)).slice(-6), ...turnRefs].map((r) => [r.n, r])).values()].sort((a, b) => a.n - b.n);
    const past = th.turns
      .slice(0, -1)
      .filter((x) => x.ans)
      .slice(-3)
      .map((x) => `问：${x.q}\n答：${String(x.ans).slice(0, 1200)}`)
      .join('\n\n');
    const user = `${past ? `之前的对话（供理解追问用，角标编号沿用）：\n\n${past}\n\n———\n\n` : ''}${shown.length ? `资料：\n\n${refBlock(shown)}` : '资料：（知识库里没有找到相关内容）'}\n\n问题：${q}`;
    const messages = [{ role: 'user', content: [{ type: 'text', text: user }] }];
    for await (const piece of llmStream(llm, answerRoute, ANSWER_SYS, messages, signal, 2000, sid)) {
      tu.ans += piece;
      emit({ t: 'delta', s: piece });
    }
    tu.done = true;
    emit({ t: 'done', model: tu.model });
  } catch (error) {
    if (error?.name === 'AbortError' || signal.aborted) {
      tu.stopped = true;
    } else {
      tu.error = String(error?.message || error);
      emit({ t: 'error', message: tu.error });
    }
  } finally {
    await save();
  }
}

function publicRef(r) {
  return {
    n: r.n,
    docId: r.docId,
    idx: r.idx,
    title: r.title,
    sourceId: r.sourceId,
    rel: r.rel,
    line: r.line,
    header: r.header,
    superseded: !!r.superseded,
    text: String(r.text || '').slice(0, 400),
  };
}

function publicThread(th) {
  return { ...th, refs: (th.refs || []).map(publicRef) };
}

/* ─────────────────────────── HTTP ─────────────────────────── */

function sendJson(res, status, payload) {
  const body = JSON.stringify(payload);
  res.writeHead(status, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' });
  res.end(body);
}

async function readJsonBody(req) {
  const chunks = [];
  for await (const chunk of req) chunks.push(chunk);
  const raw = Buffer.concat(chunks).toString('utf8');
  if (!raw) return {};
  try {
    return JSON.parse(raw);
  } catch {
    return {};
  }
}

function docTree(db) {
  const rows = db
    .prepare(
      `select d.id, d.path, d.rel_path, d.title, d.lines, d.chunk_count, d.superseded, d.source_id, s.label as source_label
       from docs d left join sources s on s.id = d.source_id order by s.label, d.rel_path`,
    )
    .all();
  const groups = new Map();
  for (const r of rows) {
    const key = r.source_id || 'unknown';
    if (!groups.has(key)) groups.set(key, { id: key, label: r.source_label || key, docs: [] });
    groups.get(key).docs.push({
      id: r.id,
      relPath: r.rel_path,
      title: r.title,
      lines: r.lines,
      chunks: r.chunk_count,
      superseded: !!r.superseded,
    });
  }
  return [...groups.values()];
}

function statsOf(db) {
  const docs = db.prepare('select count(*) c from docs').get().c;
  const chunks = db.prepare('select count(*) c from chunks').get().c;
  return { docs, chunks };
}

/* ─────────────────────────── 插件入口 ─────────────────────────── */

export function apply(ctx) {
  let db = null;
  let config = null;
  let watcher = null;
  let disposed = false;
  const ready = (async () => {
    config = await loadConfig();
    await fsp.mkdir(expand(config.dataDir || DEFAULT_DATA_DIR), { recursive: true });
    db = openDb(config.dataDir);
    try {
      state.repair = repairIndex(db);
    } catch (error) {
      state.repair = { error: String((error && error.message) || error) };
    }
    if (!disposed) {
      watcher = createWatcher(db, config);
      watcher.sync();
    }
    // 首次启动后台扫描（不阻塞启动）
    setTimeout(() => {
      scanAll(db, config).catch(() => {});
    }, 1500);
  })();

  ctx.effect(
    () => () => {
      disposed = true;
      watcher?.dispose();
    },
    'dsh-knowledge: watcher',
  );

  // 定时对账（监听的兜底）：每 10 分钟增量重扫一次（SHA-256 命中则跳过，成本极低）
  ctx.effect(() => {
    const timer = setInterval(() => {
      if (!db || !config || state.scanning) return;
      scanAll(db, config).catch(() => {});
    }, 10 * 60 * 1000);
    return () => clearInterval(timer);
  }, 'dsh-knowledge: periodic rescan');

  // Agent 工具：会话里直接查知识库
  ctx.effect(() => {
    const tools = ctx.get('tools');
    if (!tools || typeof tools.register !== 'function') return () => {};
    return tools.register({
      name: 'kb_search',
      description:
        '检索用户的本地知识库：已接入的笔记库、项目文档，以及收藏同步进来的帖子（X / 小红书 / 抖音 / YouTube 等）。用户问「某个规则/模板/参数/决策怎么定的」「依据在哪」「哪次会议说了什么」「之前收藏的某篇讲了什么」时先用它，不要凭记忆回答。返回带文件路径、标题、行号的原文片段。',
      parameters: {
        type: 'object',
        properties: {
          query: { type: 'string', description: '检索词，尽量用用户原话里的关键词' },
          limit: { type: 'integer', minimum: 1, maximum: 20, description: '返回条数，默认 8' },
        },
        required: ['query'],
      },
      output: {
        schema: { type: 'object', properties: { count: { type: 'number' }, markdown: { type: 'string' } }, required: ['count', 'markdown'] },
        render(_args, value) {
          return [{ type: 'text', text: String((value && value.markdown) || '') }];
        },
      },
      async execute(args) {
        await ready;
        const query = String((args && args.query) || '').trim();
        const limit = Math.min(Math.max(Number((args && args.limit) || 8), 1), 20);
        if (!query) return { count: 0, markdown: '缺少 query。' };
        const results = searchSmart(db, query, limit, { perDoc: 3 }).results;
        if (results.length === 0) return { count: 0, markdown: `没有检索到与「${query}」相关的内容。` };
        const lines = [`检索「${query}」，命中 ${results.length} 段：`, ''];
        results.forEach((r, i) => {
          lines.push(`### ${i + 1}. ${r.title || r.relPath}`);
          lines.push(`- 位置：\`${r.path}\` 第 ${r.line} 行${r.header ? ` · ${r.header}` : ''}${r.superseded ? ' · **已作废**' : ''}`);
          lines.push('');
          lines.push('```');
          lines.push(r.text.slice(0, 900));
          lines.push('```');
          lines.push('');
        });
        return { count: results.length, markdown: lines.join('\n') };
      },
    });
  }, 'dsh-knowledge: kb_search tool');

  // HTTP API：前端面板
  ctx.effect(
    () =>
      ctx.webServer.register({
        kind: 'prefix',
        path: '/knowledge/api',
        handler: async (req, res) => {
          const url = new URL(req.url || '/', 'http://knowledge.local');
          const rest = url.pathname.replace(/^\/knowledge\/api\/?/, '');
          try {
            await ready;
            if (rest === 'status' && req.method === 'GET') {
              const stats = statsOf(db);
              const sources = await sourcesView(db, config);
              const sel = ctx.get?.('agentDefaultModel')?.currentSelection?.();
              sendJson(res, 200, { ok: true, version: VERSION, stats, sources, state, model: sel?.model || null, watch: watchState, features: { watch: true, periodicRescan: 600, search: ['fts5', 'like', 'title'] }, config: { chunk: config.chunk, dataDir: expand(config.dataDir) } });
              return;
            }
            if (rest === 'search' && req.method === 'POST') {
              const body = await readJsonBody(req);
              const q = String(body.q || '').trim();
              const limit = Math.min(Math.max(Number(body.limit || 8), 1), 30);
              const t0 = Date.now();
              const r = q ? searchSmart(db, q, limit, { scope: body.scope, perDoc: 2 }) : { results: [], terms: [] };
              sendJson(res, 200, { ok: true, q, count: r.results.length, results: r.results, terms: r.terms, ms: Date.now() - t0 });
              return;
            }
            if (rest === 'recent' && req.method === 'GET') {
              const limit = Math.min(Math.max(Number(url.searchParams.get('limit') || 8), 1), 40);
              sendJson(res, 200, { ok: true, docs: docsOf(db, '', [], limit) });
              return;
            }
            if (rest === 'docs' && req.method === 'GET') {
              const src = url.searchParams.get('src') || '';
              sendJson(res, 200, { ok: true, docs: docsOf(db, 'where d.source_id = ?', [src], 3000) });
              return;
            }
            if (rest === 'raw' && req.method === 'GET') {
              const id = url.searchParams.get('id') || '';
              const row = db.prepare('select id, source_id, path, rel_path, title, superseded, mtime, lines from docs where id = ?').get(id);
              if (!row) {
                sendJson(res, 404, { ok: false, error: '没有这篇文档' });
                return;
              }
              let text = '';
              try {
                text = (await fsp.readFile(row.path, 'utf8')).replace(/\r\n/g, '\n');
              } catch {
                // 原文件读不到（刚被移走）：用索引里的片段拼回来
                text = db.prepare('select text from chunks where doc_id = ? order by idx').all(id).map((c) => c.text).join('\n\n');
              }
              if (text.length > 400000) text = text.slice(0, 400000) + '\n\n…（后面太长，没有显示）';
              sendJson(res, 200, { ok: true, doc: { id: row.id, sourceId: row.source_id, path: row.path, rel: row.rel_path, title: row.title, superseded: !!row.superseded, mtime: row.mtime, lines: row.lines }, text });
              return;
            }
            if (rest === 'pick-folder' && req.method === 'POST') {
              sendJson(res, 200, await pickFolder());
              return;
            }
            if (rest === 'reveal' && req.method === 'POST') {
              const body = await readJsonBody(req);
              // 只允许打开索引里有的文件或已登记的数据源，不接受任意路径
              let p = '';
              if (body.docId) p = db.prepare('select path from docs where id = ?').get(String(body.docId))?.path || '';
              else if (body.sourceId) p = expand((config.sources || []).find((s) => s.id === String(body.sourceId))?.path || '');
              if (!p) {
                sendJson(res, 404, { ok: false, error: '找不到这个文件' });
                return;
              }
              sendJson(res, 200, await revealPath(p));
              return;
            }
            if (rest === 'chats' && req.method === 'GET') {
              sendJson(res, 200, { ok: true, threads: await listThreads() });
              return;
            }
            if (rest === 'chat' && req.method === 'GET') {
              const th = await loadThread(url.searchParams.get('id'));
              if (!th) {
                sendJson(res, 404, { ok: false, error: '没有这个话题' });
                return;
              }
              sendJson(res, 200, { ok: true, thread: publicThread(th) });
              return;
            }
            if (rest === 'chat-delete' && req.method === 'POST') {
              const body = await readJsonBody(req);
              await deleteThread(body.id);
              sendJson(res, 200, { ok: true });
              return;
            }
            if (rest === 'chat' && req.method === 'POST') {
              const body = await readJsonBody(req);
              const ac = new AbortController();
              const stop = () => {
                if (!res.writableEnded) ac.abort();
              };
              req.on('close', stop);
              res.on('close', stop);
              res.writeHead(200, { 'content-type': 'application/x-ndjson; charset=utf-8', 'cache-control': 'no-store', 'x-accel-buffering': 'no' });
              res.flushHeaders?.();
              const emit = (ev) => {
                if (!res.writableEnded && !res.destroyed) res.write(JSON.stringify(ev) + '\n');
              };
              await runChat({ ctx, db, config, body, emit, signal: ac.signal });
              if (!res.writableEnded) res.end();
              return;
            }
            if (rest === 'tree' && req.method === 'GET') {
              sendJson(res, 200, { ok: true, groups: docTree(db) });
              return;
            }
            if (rest === 'doc' && req.method === 'GET') {
              const rel = url.searchParams.get('rel') || '';
              const row = db.prepare('select * from docs where rel_path = ? or id = ?').get(rel, rel);
              if (!row) {
                sendJson(res, 404, { ok: false, error: '没有这篇文档' });
                return;
              }
              const chunks = db.prepare('select idx, text, header, line from chunks where doc_id = ? order by idx').all(row.id);
              sendJson(res, 200, { ok: true, doc: row, chunks });
              return;
            }
            if (rest === 'scan' && req.method === 'POST') {
              const body = await readJsonBody(req);
              const one = body.id ? (config.sources || []).find((s) => s.id === String(body.id)) : null;
              if (one) {
                withLock(() => scanSource(db, config, one)).catch(() => {});
                sendJson(res, 200, { ok: true, started: true });
                return;
              }
              if (state.scanning) {
                sendJson(res, 200, { ok: true, already: true, state });
                return;
              }
              scanAll(db, config).catch(() => {});
              sendJson(res, 200, { ok: true, started: true });
              return;
            }
            if (rest === 'sources' && req.method === 'POST') {
              const body = await readJsonBody(req);
              const action = String(body.action || '');
              if (action === 'add') {
                const p = expand(String(body.path || '').trim());
                if (!p) {
                  sendJson(res, 400, { ok: false, error: '缺少路径' });
                  return;
                }
                let stat = null;
                try {
                  stat = await fsp.stat(p);
                } catch {
                  sendJson(res, 400, { ok: false, error: `路径不存在：${p}` });
                  return;
                }
                if (!stat.isDirectory()) {
                  sendJson(res, 400, { ok: false, error: '需要是一个文件夹' });
                  return;
                }
                const id = `src-${sha256(p).slice(0, 8)}`;
                let kind = 'folder';
                try {
                  await fsp.access(path.join(p, '.obsidian'));
                  kind = 'vault';
                } catch {
                  /* not a vault */
                }
                const label = String(body.label || path.basename(p));
                config.sources = (config.sources || []).filter((s) => s.id !== id);
                const source = { id, label, path: p, kind, enabled: true };
                config.sources.push(source);
                await saveConfig(config);
                // 加完立刻开始监听并扫一遍，不用等重启
                watcher?.sync();
                withLock(() => scanSource(db, config, source)).catch(() => {});
                sendJson(res, 200, { ok: true, source: { id, label, path: p, kind, enabled: true } });
                return;
              }
              if (action === 'remove') {
                const id = String(body.id || '');
                config.sources = (config.sources || []).filter((s) => s.id !== id);
                await saveConfig(config);
                watcher?.sync();
                await withLock(async () => {
                  for (const row of db.prepare('select id from docs where source_id = ?').all(id)) removeDoc(db, row.id);
                  db.prepare('delete from sources where id = ?').run(id);
                });
                sendJson(res, 200, { ok: true });
                return;
              }
              sendJson(res, 400, { ok: false, error: '未知 action' });
              return;
            }
            sendJson(res, 404, { ok: false, error: `未知接口 ${rest}` });
          } catch (error) {
            sendJson(res, 500, { ok: false, error: String((error && error.message) || error) });
          }
        },
      }),
    'dsh-knowledge: api',
  );

  ctx.effect(() => () => {
    try {
      db?.close();
    } catch {
      /* ignore */
    }
  }, 'dsh-knowledge: db');
}

export { searchChunks, searchSmart, queryTerms, chunkText, cjkRatio, scanAll, scanSource, openDb, loadConfig, repairIndex, createWatcher, runChat, docsOf, sourcesView, indexFile };
