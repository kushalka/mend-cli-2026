// mend: apply AI-written edits to a tree of text files (SPEC.md, version 1).
// Node 22 standard library only. In a trial the last lines hand over to runner.ts.
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];
let STRICT = false;

class Exit2 {
  readonly line: string;
  constructor(line: string) { this.line = line; }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) { this.code = code; this.path = path; }
}

const blank = (s: string): boolean => s.trim() === '';
const lead = (s: string): string => /^[ \t]*/.exec(s)![0];

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

interface Shape { lines: string[]; br: string; final: boolean }
function shape(text: string): Shape {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text === '' ? [] : text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}
function shapeText(s: Shape): string {
  return s.lines.length === 0 ? '' : s.lines.join(s.br) + (s.final ? s.br : '');
}

/** A line of the new side: `ctx` says which matched old line it repeats. */
type NLine = { text: string; ctx: number | null };
type OLine = { text: string; ctx: number | null };

function norm(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}
function occurrences(o: string[], file: string[], tier: number, from = 0): number[] {
  if (o.length === 0 || o.length > file.length) return [];
  const a = o.map((s) => norm(s, tier));
  const out: number[] = [];
  for (let i = from; i + a.length <= file.length; i += 1) {
    let k = 0;
    while (k < a.length && norm(file[i + k]!, tier) === a[k]) k += 1;
    if (k === a.length) out.push(i);
  }
  return out;
}
function findTier(o: string[], file: string[], strict: boolean, from = 0): { tier: number; hits: number[] } | null {
  for (let tier = 0; tier <= (strict ? 0 : 2); tier += 1) {
    const hits = occurrences(o, file, tier, from);
    if (hits.length > 0) return { tier, hits };
  }
  return null;
}
function rewrite(o: OLine[], n: NLine[], file: string[], pos: number, tier: number): string[] {
  const fileAt = new Map<number, string>();
  o.forEach((line, k) => { if (line.ctx !== null) fileAt.set(line.ctx, file[pos + k]!); });
  const p = o.length > 0 ? lead(o[0]!.text) : '';
  const f = o.length > 0 ? lead(file[pos]!) : '';
  return n.map((line) => {
    if (line.ctx !== null) return fileAt.get(line.ctx)!;
    if (tier !== 2 || line.text === '' || line.text.trim() === '') return line.text;
    if (p !== '' && !line.text.startsWith(p)) return line.text;
    return f + (p !== '' ? line.text.slice(p.length) : line.text);
  });
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moved = new Map<string, string>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const s0 = shape(before);
      if (line < 0 || line > s0.lines.length) throw new Fail('no-match', p);
      s0.lines.splice(line, 0, ...add);
      tree.now.set(p, shapeText(s0));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** A body line of a unified hunk or a V4A chunk. */
type BLine = { tag: ' ' | '-' | '+' | '\\'; text: string };
function bodyTag(line: string): BLine['tag'] | null {
  if (line.startsWith(' ')) return ' ';
  if (line.startsWith('-')) return '-';
  if (line.startsWith('+')) return '+';
  if (line.startsWith('\\')) return '\\';
  if (line === '') return ' ';
  return null;
}
function pair(body: BLine[]): { o: OLine[]; n: NLine[]; oRaw: string[] } {
  const o: OLine[] = [];
  const n: NLine[] = [];
  const oRaw: string[] = [];
  let ctx = 0;
  for (const l of body) {
    if (l.tag === ' ' || l.tag === '-') {
      const c = l.tag === ' ' ? ctx++ : null;
      o.push({ text: l.text, ctx: c });
      oRaw.push(l.text);
    }
    if (l.tag === ' ' || l.tag === '+') n.push({ text: l.text, ctx: l.tag === ' ' ? ctx - 1 : null });
  }
  return { o, n, oRaw };
}
function trimBody(body: BLine[]): BLine[] {
  const out = [...body];
  while (out.length > 0 && out[out.length - 1]!.tag === ' ' && out[out.length - 1]!.text === '') out.pop();
  return out;
}
function noEolAfter(body: BLine[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i += 1) if (body[i]!.tag === ' ' || body[i]!.tag === '+') last = i;
  return body.slice(last + 1).some((l) => l.tag === '\\');
}
function cleanBody(lines: BLine[]): BLine[] {
  return lines.filter((l) => l.tag !== '\\');
}

interface Hunk { a: number; body: BLine[] }
interface Section {
  diffOld: string | null; diffNew: string | null;
  minus: string | undefined | null; plus: string | undefined | null;
  renameFrom: string | null; renameTo: string | null;
  createMode: boolean; deleteMode: boolean;
  hunks: Hunk[]; paired: boolean;
}
function newSection(): Section {
  return { diffOld: null, diffNew: null, minus: undefined, plus: undefined, renameFrom: null, renameTo: null, createMode: false, deleteMode: false, hunks: [], paired: false };
}
function diffPath(text: string): string | null {
  const t = text.split('\t')[0]!.trim();
  if (t === '/dev/null') return null;
  return t.startsWith('a/') || t.startsWith('b/') ? t.slice(2) : t;
}

function applyHunks(text: string, hunks: Hunk[], strict: boolean, path: string): string {
  const s = shape(text);
  let final = s.final;
  let d = 0;
  for (const h of hunks) {
    const trimmed = trimBody(h.body);
    const body = cleanBody(trimmed);
    const { o, n, oRaw } = pair(body);
    const match = oRaw.length === 0 ? null : findTier(oRaw, s.lines, strict);
    if (oRaw.length > 0 && match === null) throw new Fail('no-match', path);
    let pos: number;
    let atEnd = false;
    let tier = 0;
    if (oRaw.length === 0) {
      pos = Math.max(0, Math.min(h.a + d, s.lines.length));
      atEnd = pos === s.lines.length;
    } else {
      const target = h.a - 1 + d;
      pos = match!.hits.reduce((best, x) => (Math.abs(x - target) < Math.abs(best - target) ? x : best), match!.hits[0]!);
      tier = match!.tier;
      atEnd = pos + oRaw.length === s.lines.length;
    }
    const written = rewrite(o, n, s.lines, pos, tier);
    s.lines.splice(pos, oRaw.length, ...written);
    d += written.length - oRaw.length;
    if (atEnd) final = !noEolAfter(trimmed);
  }
  s.final = final;
  return shapeText(s);
}

function unifiedEdits(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let sec: Section | null = null;
  let hunk: Hunk | null = null;
  const close = (): void => {
    if (hunk !== null) { sec!.hunks.push(hunk); hunk = null; }
    if (sec !== null) { edits.push(unifiedEdit(sec)); sec = null; }
  };
  for (let i = 0; i < lines.length; i += 1) {
    const l = lines[i]!;
    const newSectionHere = l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ');
    if (hunk !== null && bodyTag(l) !== null && !l.startsWith('diff --git ') && !newSectionHere) {
      hunk.body.push({ tag: bodyTag(l)!, text: l.slice(1) });
      continue;
    }
    if (hunk !== null) { sec!.hunks.push(hunk); hunk = null; }
    if (l.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.+) b\/(.+)$/.exec(l);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      close();
      sec = newSection();
      sec.diffOld = m[1]!;
      sec.diffNew = m[2]!;
    } else if (newSectionHere) {
      if (sec !== null && sec.paired) close();
      if (sec === null) sec = newSection();
      sec.minus = diffPath(l.slice(4));
      sec.plus = diffPath(lines[i + 1]!.slice(4));
      sec.paired = true;
      i += 1;
    } else if (l.startsWith('@@')) {
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(l);
      if (m === null || sec === null) throw new Exit2(`error: parse ${i + 1}`);
      hunk = { a: Number(m[1]), body: [] };
    } else if (l.startsWith('--- ') && sec !== null && !sec.paired) {
      throw new Exit2(`error: parse ${i + 2}`);
    } else if (sec !== null) {
      if (l.startsWith('rename from ')) sec.renameFrom = l.slice(12).trim();
      else if (l.startsWith('rename to ')) sec.renameTo = l.slice(10).trim();
      else if (l.startsWith('new file mode')) sec.createMode = true;
      else if (l.startsWith('deleted file mode')) sec.deleteMode = true;
    }
  }
  close();
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function unifiedEdit(sec: Section): Edit {
  let oldPath = sec.minus !== undefined ? sec.minus : (sec.renameFrom ?? sec.diffOld);
  let newPath = sec.plus !== undefined ? sec.plus : (sec.renameTo ?? sec.diffNew);
  if (sec.createMode) oldPath = null;
  if (sec.deleteMode) newPath = null;
  return (tree) => {
    if (typeof oldPath === 'string' && !safe(oldPath)) throw new Fail('unsafe', oldPath);
    if (typeof newPath === 'string' && !safe(newPath)) throw new Fail('unsafe', newPath);
    if (oldPath === null && newPath !== null) {
      if (tree.get(newPath) !== null) throw new Fail('exists', newPath);
      const plus = sec.hunks.flatMap((h) => cleanBody(trimBody(h.body)).filter((l) => l.tag === '+').map((l) => l.text));
      const allBodies = sec.hunks.flatMap((h) => trimBody(h.body));
      const noEol = noEolAfter(allBodies);
      tree.now.set(newPath, plus.length === 0 ? '' : plus.join('\n') + (noEol ? '' : '\n'));
      return;
    }
    if (typeof oldPath !== 'string') throw new Fail('missing', newPath ?? '');
    const before = tree.get(oldPath);
    if (before === null) throw new Fail('missing', oldPath);
    if (newPath === null) { tree.now.set(oldPath, null); return; }
    const moved = newPath !== oldPath;
    if (moved && tree.get(newPath) !== null) throw new Fail('exists', newPath);
    const out = applyHunks(before, sec.hunks, STRICT, oldPath);
    if (moved) { tree.now.set(oldPath, null); tree.now.set(newPath, out); tree.moved.set(newPath, oldPath); }
    else tree.now.set(oldPath, out);
  };
}

function searchReplaceEdits(lines: string[]): Edit[] {
  const edits: Edit[] = [];
  let start = 0;
  let lastPath: string | null = null;
  for (;;) {
    let s = -1;
    for (let i = start; i < lines.length; i += 1) if (lines[i]!.trimEnd() === '<<<<<<< SEARCH') { s = i; break; }
    if (s < 0) break;
    let p: string | null = null;
    for (let j = s - 1; j >= start; j -= 1) {
      const t = lines[j]!.trim();
      if (t !== '' && !t.startsWith('```')) { p = t; break; }
    }
    if (p === null) p = lastPath;
    if (p === null) throw new Exit2(`error: parse ${s + 1}`);
    let eq = -1;
    let rp = -1;
    for (let j = s + 1; j < lines.length; j += 1) {
      if (eq < 0 && lines[j]!.trimEnd() === '=======') { eq = j; continue; }
      if (eq >= 0 && lines[j]!.trimEnd() === '>>>>>>> REPLACE') { rp = j; break; }
    }
    if (eq < 0 || rp < 0) throw new Exit2(`error: parse ${s + 1}`);
    const oldText = lines.slice(s + 1, eq);
    const newText = lines.slice(eq + 1, rp);
    const path = p;
    lastPath = path;
    start = rp + 1;
    edits.push((tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (oldText.length === 0) {
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, shapeText({ lines: newText, br: '\n', final: true }));
        return;
      }
      const before = tree.get(path);
      if (before === null) throw new Fail('missing', path);
      const s0 = shape(before);
      const match = findTier(oldText, s0.lines, STRICT);
      if (match === null) throw new Fail('no-match', path);
      if (match.hits.length > 1) throw new Fail('ambiguous', path);
      const o: OLine[] = oldText.map((text) => ({ text, ctx: null }));
      const n: NLine[] = newText.map((text) => ({ text, ctx: null }));
      s0.lines.splice(match.hits[0]!, oldText.length, ...rewrite(o, n, s0.lines, match.hits[0]!, match.tier));
      tree.now.set(path, shapeText(s0));
    });
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function v4aEdits(lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last -= 1;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    if (blank(lines[i]!)) { i += 1; continue; }
    const l = lines[i]!;
    const add = /^\*\*\* Add File: (.*)$/.exec(l);
    const del = /^\*\*\* Delete File: (.*)$/.exec(l);
    const upd = /^\*\*\* Update File: (.*)$/.exec(l);
    if (!add && !del && !upd) throw new Exit2(`error: parse ${i + 1}`);
    const path = (add ?? del ?? upd)![1]!.trim();
    const bodyStart = i + 1;
    let end = bodyStart;
    while (end < last && !/^\*\*\* (Add|Delete|Update) File: /.test(lines[end]!)) end += 1;
    let body = lines.slice(bodyStart, end);
    while (body.length > 0 && blank(body[body.length - 1]!)) body.pop();
    i = end;
    if (add) {
      body.forEach((x, k) => { if (x !== '' && !x.startsWith('+')) throw new Exit2(`error: parse ${bodyStart + k + 1}`); });
      const fileLines = body.map((x) => (x === '' ? '' : x.slice(1)));
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      continue;
    }
    if (del) {
      const bad = body.findIndex((x) => !blank(x));
      if (bad >= 0) throw new Exit2(`error: parse ${bodyStart + bad + 1}`);
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
      continue;
    }
    let move: string | null = null;
    let k = 0;
    if (body.length > 0 && body[0]!.startsWith('*** Move to: ')) { move = body[0]!.slice(13).trim(); k = 1; }
    type Chunk = { anchor: string | null; eof: boolean; body: BLine[] };
    const chunks: Chunk[] = [];
    let cur: Chunk | null = null;
    for (; k < body.length; k += 1) {
      const x = body[k]!;
      if (x.startsWith('@@')) {
        if (cur !== null) chunks.push(cur);
        cur = { anchor: x.slice(2).trim(), eof: false, body: [] };
        continue;
      }
      if (x.trim() === '*** End of File') {
        if (cur === null) cur = { anchor: null, eof: true, body: [] };
        else cur.eof = true;
        chunks.push(cur);
        cur = null;
        continue;
      }
      const tag = bodyTag(x);
      if (tag === null) throw new Exit2(`error: parse ${bodyStart + k + 1}`);
      if (cur === null) {
        if (chunks.length > 0) throw new Exit2(`error: parse ${bodyStart + k + 1}`);
        cur = { anchor: null, eof: false, body: [] };
      }
      cur.body.push({ tag, text: x.slice(1) });
    }
    if (cur !== null) chunks.push(cur);
    if (chunks.length === 0 && move === null) throw new Exit2(`error: parse ${bodyStart}`);
    edits.push((tree) => {
      if (!safe(path)) throw new Fail('unsafe', path);
      if (move !== null && !safe(move)) throw new Fail('unsafe', move);
      const before = tree.get(path);
      if (before === null) throw new Fail('missing', path);
      if (move !== null && tree.get(move) !== null) throw new Fail('exists', move);
      const s0 = shape(before);
      let cursor = 0;
      for (const chunk of chunks) {
        if (chunk.anchor !== null && chunk.anchor !== '') {
          const found = findTier([chunk.anchor], s0.lines, STRICT, cursor);
          if (found === null) throw new Fail('no-match', path);
          cursor = found.hits[0]! + 1;
        }
        const trimmed = trimBody(chunk.body);
        const { o, n, oRaw } = pair(cleanBody(trimmed));
        let pos: number;
        let tier = 0;
        let foundEof = false;
        if (chunk.eof) {
          if (oRaw.length === 0) { pos = s0.lines.length; foundEof = true; }
          else {
            for (let t = 0; t <= (STRICT ? 0 : 2); t += 1) {
              const hit = occurrences(oRaw, s0.lines, t, cursor).find((h) => h + oRaw.length === s0.lines.length);
              if (hit !== undefined) { tier = t; pos = hit; foundEof = true; break; }
            }
            if (!foundEof) throw new Fail('no-match', path);
          }
        } else if (oRaw.length === 0) pos = Math.min(cursor, s0.lines.length);
        else {
          const found = findTier(oRaw, s0.lines, STRICT, cursor);
          if (found === null) throw new Fail('no-match', path);
          pos = found.hits[0]!;
          tier = found.tier;
        }
        const written = rewrite(o, n, s0.lines, pos, tier);
        s0.lines.splice(pos, oRaw.length, ...written);
        cursor = pos + written.length;
      }
      if (move !== null) { tree.now.set(path, null); tree.now.set(move, shapeText(s0)); tree.moved.set(move, path); }
      else tree.now.set(path, shapeText(s0));
    });
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  STRICT = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !STRICT) STRICT = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines);
    else if (kind === 'v4a') edits = v4aEdits(lines);
    else throw new Exit2('error: format');
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: string[] = [];
  const moveRows = new Set<string>();
  const moveFroms = new Set<string>();
  for (const [to, from] of tree.moved) {
    if (tree.original(from) !== null && tree.now.get(from) === null && tree.original(to) === null && tree.now.get(to) !== null) {
      moveRows.add(to);
      moveFroms.add(from);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (moveFroms.has(p)) {
      if (check) continue;
      if (now === null) rmSync(p, { force: true });
      else { mkdirSync(dirname(p), { recursive: true }); writeFileSync(p, now); }
      continue;
    }
    if (moveRows.has(p)) rows.push(`R ${tree.moved.get(p)!} -> ${p}`);
    else rows.push(`${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`);
    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
