/* 互動式一階邏輯證明助手 — 核心(Node 與瀏覽器共用)
   結構:解析器 → 可信核心 check()(唯一決定證明對錯的部分)→ 策略層(只負責產生證明項)→ 報告 */
(function () {
'use strict';
const BOT = { t: 'bot' };
const GREEK = { '∀': ' forall ', '∃': ' exists ', '¬': '~', '∧': '&', '∨': '|', '→': '->', '↔': '<->', '⊥': ' False ' };
const lex = s => s.replace(/[∀∃¬∧∨→↔⊥]/g, c => GREEK[c]).replace(/\/\\/g, '&').replace(/\\\//g, '|').match(/<->|->|[A-Za-z_][\w']*|\S/g) || [];

/* ── 解析:~A 展開成 A→⊥,A↔B 展開成 (A→B)∧(B→A) ── */
function P(src) {
  const T = lex(src); let p = 0;
  const err = m => new Error(`${m}(附近:${T.slice(Math.max(0, p - 3), p + 1).join(' ') || '結尾'})`);
  const expect = t => { if (T[p++] !== t) throw err(`語法錯誤:預期 "${t}"`); };
  const ident = () => { const x = T[p++]; if (!x || !/^[A-Za-z_]/.test(x)) throw err('語法錯誤:這裡需要名稱'); return x; };
  const list = f => { const a = [f()]; while (T[p] === ',') { p++; a.push(f()); } expect(')'); return a; };
  const term = () => { const n = ident(); if (T[p] === '(') { p++; return { f: n, a: list(term) }; } return { v: n }; };
  const iff = () => { let l = imp(); while (T[p] === '<->') { p++; const r = imp(); l = { t: 'and', l: { t: 'imp', l, r }, r: { t: 'imp', l: r, r: l } }; } return l; };
  const imp = () => { const l = or(); if (T[p] === '->') { p++; return { t: 'imp', l, r: imp() }; } return l; };
  const or = () => { let l = and(); while (T[p] === '|') { p++; l = { t: 'or', l, r: and() }; } return l; };
  const and = () => { let l = un(); while (T[p] === '&') { p++; l = { t: 'and', l, r: un() }; } return l; };
  const un = () => {
    const x = T[p];
    if (x === '~') { p++; return { t: 'imp', l: un(), r: BOT }; }
    if (x === 'forall' || x === 'exists') {
      p++; const vs = [];
      while (T[p] !== '.' && T[p] !== ',') { if (T[p] === undefined || T[p] === '(') throw err('語法錯誤:量詞變數後面需要加上 "."'); vs.push(ident()); }
      p++; const f = iff();
      return vs.reduceRight((b, v) => ({ t: x === 'forall' ? 'all' : 'ex', v, f: b }), f);
    }
    if (x === '(') { p++; const f = iff(); expect(')'); return f; }
    const n = ident(); if (n === 'False') return BOT; if (n === 'True') return { t: 'imp', l: BOT, r: BOT };
    let a = []; if (T[p] === '(') { p++; a = list(term); }
    return { t: 'atom', n, a };
  };
  return { iff, term, ident, err, peek: () => T[p], next: () => T[p++], done: () => p >= T.length };
}
const parseF = s => { const q = P(s); const f = q.iff(); if (!q.done()) throw q.err('語法錯誤:多餘的符號'); return f; };

/* ── 顯示 ── */
const par = (s, c) => c ? '(' + s + ')' : s;
const pt = t => t.v !== undefined ? t.v : t.f + '(' + t.a.map(pt).join(', ') + ')';
function fm(f, q = 0) {
  switch (f.t) {
    case 'bot': return 'False';
    case 'atom': return f.n + (f.a.length ? '(' + f.a.map(pt).join(', ') + ')' : '');
    case 'imp': return f.r.t === 'bot' ? (f.l.t === 'bot' ? 'True' : '¬' + fm(f.l, 4)) : par(fm(f.l, 2) + ' → ' + fm(f.r, 1), q > 1);
    case 'or': return par(fm(f.l, 2) + ' ∨ ' + fm(f.r, 3), q > 2);
    case 'and': return par(fm(f.l, 3) + ' ∧ ' + fm(f.r, 4), q > 3);
    default: return par((f.t === 'all' ? '∀ ' : '∃ ') + f.v + ', ' + fm(f.f, 0), q > 0);
  }
}

/* ── 公式工具:α 等價、自由變數、代換(避免變數捕獲) ── */
const kt = (t, e) => t.v !== undefined ? (e[t.v] || 'v:' + t.v) : t.f + '(' + t.a.map(x => kt(x, e)).join(',') + ')';
const key = (f, e = {}, d = 0) => f.t === 'bot' ? '⊥' : f.t === 'atom' ? f.n + '(' + f.a.map(t => kt(t, e)).join(',') + ')'
  : f.t === 'all' || f.t === 'ex' ? f.t + '.' + key(f.f, { ...e, [f.v]: '#' + d }, d + 1) : f.t + '(' + key(f.l, e, d) + ',' + key(f.r, e, d) + ')';
const eq = (a, b) => key(a) === key(b);
const fvt = (t, s = new Set()) => { t.v !== undefined ? s.add(t.v) : t.a.forEach(x => fvt(x, s)); return s; };
function fv(f, s = new Set(), b = []) {
  if (f.t === 'atom') f.a.forEach(t => fvt(t).forEach(v => b.includes(v) || s.add(v)));
  else if (f.t === 'all' || f.t === 'ex') fv(f.f, s, [...b, f.v]);
  else if (f.t !== 'bot') { fv(f.l, s, b); fv(f.r, s, b); }
  return s;
}
const st = (t, x, u) => t.v !== undefined ? (t.v === x ? u : t) : { f: t.f, a: t.a.map(y => st(y, x, u)) };
function sub(f, x, u) {
  if (f.t === 'bot') return f;
  if (f.t === 'atom') return { ...f, a: f.a.map(t => st(t, x, u)) };
  if (f.t === 'all' || f.t === 'ex') {
    if (f.v === x) return f;
    let v = f.v, b = f.f;
    if (fvt(u).has(v)) { const bad = new Set([...fvt(u), ...fv(f.f), x]); let n = v; while (bad.has(n)) n += "'"; b = sub(b, v, { v: n }); v = n; }
    return { t: f.t, v, f: sub(b, x, u) };
  }
  return { t: f.t, l: sub(f.l, x, u), r: sub(f.r, x, u) };
}
const look = (ctx, n) => { for (let i = ctx.length; i--; ) if (ctx[i][0] === n) return ctx[i][1]; };

/* ── 可信核心:檢查證明項,回傳它證明的命題。策略寫錯只會失敗,不會讓錯誤的證明通過 ── */
function check(p, ctx, fl = {}) {
  const C = (q, c = ctx) => check(q, c, fl);
  const bad = m => { throw new Error('核心檢查失敗:' + m); };
  const need = (f, t, m) => f.t === t ? f : bad(m + ' 的對象形狀不對');
  switch (p.r) {
    case 'hyp': return look(ctx, p.n) || bad('找不到假設 ' + p.n);
    case 'sorry': fl.sorry = true; return p.f;
    case 'meta': return bad('仍有未解決的目標');
    case 'let': return C(p.q, [...ctx, [p.n, C(p.p)]]);
    case 'andI': return { t: 'and', l: C(p.a), r: C(p.b) };
    case 'andE1': return need(C(p.p), 'and', '∧ 消去').l;
    case 'andE2': return need(C(p.p), 'and', '∧ 消去').r;
    case 'orI1': return { t: 'or', l: C(p.p), r: p.f };
    case 'orI2': return { t: 'or', l: p.f, r: C(p.p) };
    case 'orE': { const o = need(C(p.p), 'or', '∨ 消去'), a = C(p.a, [...ctx, [p.x, o.l]]), b = C(p.b, [...ctx, [p.y, o.r]]); return eq(a, b) ? a : bad('∨ 消去的兩個分支結論不同'); }
    case 'impI': return { t: 'imp', l: p.f, r: C(p.p, [...ctx, [p.h, p.f]]) };
    case 'impE': { const i = need(C(p.f), 'imp', '→ 消去'); return eq(i.l, C(p.a)) ? i.r : bad('→ 消去的前提不吻合'); }
    case 'botE': need(C(p.p), 'bot', '⊥ 消去'); return p.f;
    case 'dne': { const f = need(C(p.p), 'imp', '反證'); return f.r.t === 'bot' && f.l.t === 'imp' && f.l.r.t === 'bot' ? f.l.l : bad('反證需要 ¬¬A'); }
    case 'allI': { if (ctx.some(([, f]) => fv(f).has(p.v))) bad(`變數 ${p.v} 出現在假設中,不能一般化`); return { t: 'all', v: p.v, f: C(p.p) }; }
    case 'allE': { const a = need(C(p.p), 'all', '∀ 消去'); return sub(a.f, a.v, p.t); }
    case 'exI': return eq(C(p.p), sub(p.f, p.v, p.t)) ? { t: 'ex', v: p.v, f: p.f } : bad('∃ 引入的見證不吻合');
    case 'exE': {
      const e = need(C(p.p), 'ex', '∃ 消去'), r = C(p.q, [...ctx, [p.h, sub(e.f, e.v, { v: p.x })]]);
      if (fv(r).has(p.x) || fv(e).has(p.x) || ctx.some(([, f]) => fv(f).has(p.x))) bad(`變數 ${p.x} 不夠新`);
      return r;
    }
  }
  return bad('未知的規則 ' + p.r);
}

/* ── 策略層:每個策略把第一個目標換成新目標,並給它指派一個含洞(meta)的證明項 ── */
function app(src, ctx) { // 解析 "h t m":假設 h 依序套用項(∀ 消去)或假設(→ 消去)
  const q = P(src), n = q.ident(); let F = look(ctx, n), pf = { r: 'hyp', n };
  if (!F) throw new Error(`找不到假設 ${n}`);
  while (!q.done()) {
    const t = q.peek(), A = /^[A-Za-z_]/.test(t) && look(ctx, t);
    if (A) {
      q.next();
      if (F.t !== 'imp' || !eq(F.l, A)) throw new Error(`假設 ${t} 無法餵給 ${fm(F)}` + (F.t === 'imp' ? `:這裡需要 ${fm(F.l)}` : ''));
      pf = { r: 'impE', f: pf, a: { r: 'hyp', n: t } }; F = F.r;
    } else {
      const tm = q.term();
      if (F.t !== 'all') throw new Error(`無法把 ${pt(tm)} 代入 ${fm(F)},它不是 ∀`);
      pf = { r: 'allE', p: pf, t: tm }; F = sub(F.f, F.v, tm);
    }
  }
  return [pf, F];
}
function tactic(S, name, arg) {
  const g = S.goals[0]; if (!g) throw new Error('已經沒有目標了');
  const { ctx, f } = g, M = x => ({ r: 'meta', id: x.id });
  const solve = (pf, gs = []) => { S.assign[g.id] = pf; S.goals = [...gs, ...S.goals.slice(1)]; };
  const ng = (c, f2, v = g.vars) => S.mk(c, v, f2);
  const hyp = n => look(ctx, n) || (() => { throw new Error(`找不到假設 ${n}`); })();
  const ws = arg.trim() ? arg.trim().split(/\s+/) : [];
  const is = (t, m) => { if (f.t !== t) throw new Error(`${name} 不適用:目標是 ${fm(f)}${m || ''}`); };
  const fresh = x => { if (fv(f).has(x) || ctx.some(([, h]) => fv(h).has(x))) throw new Error(`變數名 ${x} 已被使用,請換一個名稱`); };
  switch (name) {
    case 'intro': {
      const h = ws[0] || (f.t === 'all' ? 'x' : 'h');
      if (f.t === 'imp') { const n = ng([...ctx, [h, f.l]], f.r); return solve({ r: 'impI', h, f: f.l, p: M(n) }, [n]); }
      is('all', '(需要 → 或 ∀)'); fresh(h);
      const n = ng(ctx, sub(f.f, f.v, { v: h }), [...g.vars, h]); return solve({ r: 'allI', v: h, p: M(n) }, [n]);
    }
    case 'exact': { const [pf, F] = app(arg, ctx); if (!eq(F, f)) throw new Error(`exact 的型別不吻合:得到 ${fm(F)},但目標是 ${fm(f)}`); return solve(pf); }
    case 'assumption': { for (let i = ctx.length; i--; ) if (eq(look(ctx, ctx[i][0]), f)) return solve({ r: 'hyp', n: ctx[i][0] }); throw new Error('找不到符合目標的假設'); }
    case 'apply': {
      const [pf, F] = app(arg, ctx), prem = []; let c = F;
      while (!eq(c, f)) { if (c.t !== 'imp') throw new Error(`apply 失敗:${fm(F)} 的結論無法吻合目標 ${fm(f)}`); prem.push(c.l); c = c.r; }
      const gs = prem.map(a => ng(ctx, a));
      return solve(gs.reduce((p, x) => ({ r: 'impE', f: p, a: M(x) }), pf), gs);
    }
    case 'constructor': { is('and', '(↔ 已展開成 ∧)'); const a = ng(ctx, f.l), b = ng(ctx, f.r); return solve({ r: 'andI', a: M(a), b: M(b) }, [a, b]); }
    case 'left': case 'right': { is('or'); const L = name === 'left', n = ng(ctx, L ? f.l : f.r); return solve({ r: L ? 'orI1' : 'orI2', p: M(n), f: L ? f.r : f.l }, [n]); }
    case 'exists': { is('ex'); const q = P(arg), t = q.term(); if (!q.done()) throw q.err('語法錯誤:多餘的符號'); const n = ng(ctx, sub(f.f, f.v, t)); return solve({ r: 'exI', t, p: M(n), v: f.v, f: f.f }, [n]); }
    case 'exfalso': { const n = ng(ctx, BOT); return solve({ r: 'botE', p: M(n), f }, [n]); }
    case 'by_contra': { const h = ws[0] || 'h', neg = { t: 'imp', l: f, r: BOT }, n = ng([...ctx, [h, neg]], BOT); return solve({ r: 'dne', p: { r: 'impI', h, f: neg, p: M(n) } }, [n]); }
    case 'cases': {
      const [h, a = 'h1', b = 'h2'] = ws.filter(x => x !== 'with'), A = hyp(h), H = { r: 'hyp', n: h };
      if (A.t === 'and') { const n = ng([...ctx, [a, A.l], [b, A.r]], f); return solve({ r: 'let', n: a, p: { r: 'andE1', p: H }, q: { r: 'let', n: b, p: { r: 'andE2', p: H }, q: M(n) } }, [n]); }
      if (A.t === 'or') { const n1 = ng([...ctx, [a, A.l]], f), n2 = ng([...ctx, [b, A.r]], f); return solve({ r: 'orE', p: H, x: a, a: M(n1), y: b, b: M(n2) }, [n1, n2]); }
      if (A.t === 'ex') { fresh(a); if (fv(A).has(a)) throw new Error(`變數名 ${a} 已被使用`); const n = ng([...ctx, [b, sub(A.f, A.v, { v: a })]], f, [...g.vars, a]); return solve({ r: 'exE', p: H, x: a, h: b, q: M(n) }, [n]); }
      throw new Error(`cases 不適用:${h} 是 ${fm(A)}`);
    }
    case 'have': {
      const m = arg.match(/^([\w']+)\s*(:=|:)\s*(.+)$/); if (!m) throw new Error('格式:have 名稱 : 命題  或  have 名稱 := 假設 參數…');
      if (m[2] === ':=') { const [pf, F] = app(m[3], ctx), n = ng([...ctx, [m[1], F]], f); return solve({ r: 'let', n: m[1], p: pf, q: M(n) }, [n]); }
      const F = parseF(m[3]), n1 = ng(ctx, F), n2 = ng([...ctx, [m[1], F]], f); return solve({ r: 'let', n: m[1], p: M(n1), q: M(n2) }, [n1, n2]);
    }
    case 'show': if (!eq(parseF(arg), f)) throw new Error(`show 不吻合:目標是 ${fm(f)}`); return;
    case 'sorry': S.sorry = true; return solve({ r: 'sorry', f });
  }
  throw new Error(`未知的策略 ${name}`);
}

/* ── 執行一個定理 ── */
const inst = (p, A) => Array.isArray(p) ? p.map(x => inst(x, A)) : p && typeof p === 'object'
  ? (p.r === 'meta' ? inst(A[p.id], A) : Object.fromEntries(Object.entries(p).map(([k, v]) => [k, inst(v, A)]))) : p;
const sx = p => p.r === 'hyp' ? p.n : '(' + p.r + Object.entries(p).filter(([k]) => k !== 'r').map(([, v]) => ' ' + (v && v.r ? sx(v) : typeof v === 'string' ? v : v && v.t ? fm(v) : v && (v.v !== undefined || v.f) ? pt(v) : '')).join('') + ')';

function runThm(text) {
  const L = text.split('\n').map(l => l.replace(/--.*$/, ''));
  const hi = L.findIndex(l => /^\s*theorem\b/.test(l)); if (hi < 0) throw new Error('找不到 theorem 宣告');
  const m = L[hi].trim().match(/^theorem\s+([\w']+)\s*(.*?)\s*:=\s*by\s*$/);
  if (!m) throw new Error('標頭格式:theorem 名稱 (h : 前提) : 結論 := by');
  let rest = m[2]; const ctx = [];
  while (rest.startsWith('(')) {
    let d = 0, i = 0; for (; i < rest.length; i++) { if (rest[i] === '(') d++; if (rest[i] === ')' && !--d) break; }
    const b = rest.slice(1, i), c = b.indexOf(':'); if (c < 0) throw new Error('前提格式:(名稱 : 命題)');
    ctx.push([b.slice(0, c).trim(), parseF(b.slice(c + 1))]); rest = rest.slice(i + 1).trim();
  }
  if (!rest.startsWith(':')) throw new Error('標頭缺少 ":" 與結論');
  const F = parseF(rest.slice(1)); let n = 0;
  const S = { goals: [], assign: {}, sorry: false, mk: (c, v, f) => ({ id: ++n, ctx: c, vars: v, f }) };
  const g0 = S.mk(ctx, [], F); S.goals = [g0];
  const states = { [hi]: S.goals }, errors = {}; let failed = false;
  for (let i = hi + 1; i < L.length; i++) {
    const t = L[i].trim().replace(/^[·•*-]\s+/, '');
    if (t && !failed) {
      try { const mm = t.match(/^(\w+)\s*(.*)$/); if (!mm) throw new Error('看不懂這一行'); tactic(S, mm[1], mm[2]); }
      catch (e) { errors[i] = e.message; failed = true; }
    }
    states[i] = S.goals;
  }
  const r = { name: m[1], goal: F, hi, states, errors, lines: L, status: 'error' };
  if (failed) return r;
  if (S.goals.length) { r.status = 'open'; return r; }
  try {
    const pf = inst(S.assign[g0.id], S.assign), fl = {};
    if (!eq(check(pf, ctx, fl), F)) throw new Error('核心推出的命題與宣告不符');
    r.status = fl.sorry ? 'sorry' : 'done'; r.term = sx(pf);
  } catch (e) { r.status = 'kernel'; r.detail = e.message; }
  return r;
}

/* ── 輸出 ── */
const showGoal = g => [...(g.vars.length ? [g.vars.join(' ') + ' : 項'] : []), ...g.ctx.map(([n, f]) => n + ' : ' + fm(f)), '⊢ ' + fm(g.f)].join('\n');
const showGoals = gs => gs.length ? (gs.length > 1 ? gs.length + ' 個目標\n\n' : '') + gs.map(showGoal).join('\n\n') : '沒有目標了';
const statusText = r => ({ done: '✔ 證明完成,核心檢查通過', sorry: '⚠ 證明完成,但含有 sorry(未真正證明)', error: '✘ 有策略執行失敗',
  open: '… 證明尚未完成,還有目標', kernel: '✘ 核心拒絕了這個證明:' + r.detail }[r.status]);
const splitThms = t => t.split(/(?=^\s*theorem\b)/m).filter(s => /^\s*theorem\b/.test(s));
function report(r, trace) {
  const ind = (s, k) => s.split('\n').map(x => ' '.repeat(k) + x);
  const o = [`theorem ${r.name} : ${fm(r.goal)}`];
  if (trace) for (let i = r.hi + 1; i < r.lines.length; i++) if (r.lines[i].trim() && !(i in r.errors)) o.push('  ' + r.lines[i].trim(), ...ind(showGoals(r.states[i]), 6));
  for (const [i, m] of Object.entries(r.errors)) o.push(`第 ${+i + 1} 行錯誤:${m}`, ...ind(showGoals(r.states[i]), 4));
  if (r.status === 'open') o.push(...ind(showGoals(r.states[r.lines.length - 1]), 2));
  return o.concat(statusText(r)).join('\n');
}

const examples = [
  { name: '∧ 交換律', src: 'theorem and_swap : P & Q -> Q & P := by\n  intro h\n  cases h with hp hq\n  constructor\n  exact hq\n  exact hp' },
  { name: '假言三段論', src: 'theorem syllogism (h1 : P -> Q) (h2 : Q -> R) : P -> R := by\n  intro hp\n  apply h2\n  apply h1\n  exact hp' },
  { name: '∨ 交換律', src: 'theorem or_comm : P | Q -> Q | P := by\n  intro h\n  cases h with hp hq\n  right\n  exact hp\n  left\n  exact hq' },
  { name: '雙重否定消去(古典)', src: 'theorem dne : ~~P -> P := by\n  intro h\n  by_contra hn\n  exact h hn' },
  { name: 'Peirce’s law', src: 'theorem peirce : ((P -> Q) -> P) -> P := by\n  intro h\n  by_contra hn\n  apply hn\n  apply h\n  intro hp\n  exfalso\n  exact hn hp' },
  { name: '蘇格拉底三段論', src: 'theorem socrates (h : forall x. Man(x) -> Mortal(x)) (m : Man(socrates)) : Mortal(socrates) := by\n  exact h socrates m' },
  { name: '∀ 對 ∧ 分配', src: 'theorem all_and : (forall x. P(x) & Q(x)) -> (forall x. P(x)) & (forall x. Q(x)) := by\n  intro h\n  constructor\n  intro y\n  have hy := h y\n  cases hy with a b\n  exact a\n  intro z\n  have hz := h z\n  cases hz with a b\n  exact b' },
  { name: '∃ 與 ∀ 的對偶', src: 'theorem ex_not_all : (exists x. P(x)) -> ~(forall x. ~P(x)) := by\n  intro h\n  intro hn\n  cases h with x hx\n  exact hn x hx' },
];
const API = { runThm, splitThms, report, statusText, showGoals, check, parseF, fm, examples };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else globalThis.Lean = API;
})();
