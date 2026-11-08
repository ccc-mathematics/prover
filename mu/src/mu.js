/* μ — 微型 CIC 證明助手(Node 與瀏覽器共用)
   ① 核心:locally nameless 的項、宇宙階層、β δ ι 化簡、定義等價、型別推導
   ② 歸納型別:正向性檢查 + 自動生成遞迴子(I.ind 目標 Prop、I.rec 目標 Type)
   ③ elaborator:隱式參數、洞 _、合一   ④ 策略   ⑤ 以上機制定義的標準庫(prelude) */
(function () {
'use strict';
class MuError extends Error {}
const die = m => { throw new MuError(m); };

/* ── ① 核心 ── 項:b 綁定變數(de Bruijn)、f 區域變數、s 宇宙(0=Prop,1=Type,2=Type 1…)、c 常數、a 應用、l λ、p Π、m 洞 */
const B = i => ({ k: 'b', i }), S = l => ({ k: 's', l }), C = n => ({ k: 'c', n }), A = (f, a) => ({ k: 'a', f, a });
const Lam = (n, ty, b, imp) => ({ k: 'l', n, ty, b, imp }), Pi = (n, ty, b, imp) => ({ k: 'p', n, ty, b, imp });
let uid = 0, G = {}, MS = [], trail = [], hid = 0; const FL = {};
const FV = (n, ty, imp) => ({ k: 'f', id: ++uid, n, ty, imp });
const newMeta = (ty, lc) => { const m = { k: 'm', id: ++uid, ty, sol: null, lc }; MS.push(m); return m; };
const deref = t => { while (t.k === 'm' && t.sol) t = t.sol; return t; };
const spine = t => { const a = []; t = deref(t); while (t.k === 'a') { a.unshift(t.a); t = deref(t.f); } return [t, a]; };
const inst = (t, v, d = 0) => t.k === 'b' ? (t.i === d ? v : t) : t.k === 'a' ? A(inst(t.f, v, d), inst(t.a, v, d))
  : t.k === 'l' || t.k === 'p' ? { ...t, ty: inst(t.ty, v, d), b: inst(t.b, v, d + 1) } : t.k === 'z' ? { ...t, ty: inst(t.ty, v, d) } : t;
const abs = (t, x, d = 0) => { t = deref(t); return t.k === 'f' ? (t.id === x.id ? B(d) : t) : t.k === 'a' ? A(abs(t.f, x, d), abs(t.a, x, d))
  : t.k === 'l' || t.k === 'p' ? { ...t, ty: abs(t.ty, x, d), b: abs(t.b, x, d + 1) } : t.k === 'z' ? { ...t, ty: abs(t.ty, x, d) } : t; };
const mkPi = (fs, b) => fs.reduceRight((r, x) => Pi(x.n, x.ty, abs(r, x), x.imp), b);
const mkLam = (fs, b) => fs.reduceRight((r, x) => Lam(x.n, zk(x.ty), abs(r, x), x.imp), b);
const zk = t => { t = deref(t); return t.k === 'a' ? A(zk(t.f), zk(t.a)) : t.k === 'l' || t.k === 'p' ? { ...t, ty: zk(t.ty), b: zk(t.b) } : t; };
const usesB = (t, j = 0) => { t = deref(t); return t.k === 'b' ? t.i === j : t.k === 'a' ? usesB(t.f, j) || usesB(t.a, j) : t.k === 'l' || t.k === 'p' ? usesB(t.ty, j) || usesB(t.b, j + 1) : false; };
const eqT = (a, b) => { a = deref(a); b = deref(b); if (a === b) return true; if (a.k !== b.k) return false;
  switch (a.k) { case 'b': return a.i === b.i; case 'f': return a.id === b.id; case 'c': return a.n === b.n; case 's': return a.l === b.l;
    case 'a': return eqT(a.f, b.f) && eqT(a.a, b.a); case 'l': case 'p': return eqT(a.ty, b.ty) && eqT(a.b, b.b); } return false; };
const absT = (t, l, d = 0) => { t = deref(t); if (eqT(t, l)) return B(d); return t.k === 'a' ? A(absT(t.f, l, d), absT(t.a, l, d))
  : t.k === 'l' || t.k === 'p' ? { ...t, ty: absT(t.ty, l, d), b: absT(t.b, l, d + 1) } : t; };
const hb = t => { t = deref(t); if (t.k === 'a') { const f = deref(t.f); if (f.k === 'l') return inst(f.b, t.a); } return t; };
const hbs = t => { for (;;) { t = deref(t); const [h, sp] = spine(t); if (h.k === 'l' && sp.length) { t = sp.slice(1).reduce(A, inst(h.b, sp[0])); continue; } return t; } };
const occF = (t, x) => { t = deref(t); return t.k === 'f' ? t.id === x.id : t.k === 'a' ? occF(t.f, x) || occF(t.a, x) : t.k === 'l' || t.k === 'p' ? occF(t.ty, x) || occF(t.b, x) : false; };
const mentions = (t, n) => { t = deref(t); return t.k === 'c' ? t.n === n : t.k === 'a' ? mentions(t.f, n) || mentions(t.a, n) : t.k === 'l' || t.k === 'p' ? mentions(t.ty, n) || mentions(t.b, n) : false; };
const metasOf = (t, acc = []) => { t = deref(t); if (t.k === 'm') { if (!acc.includes(t)) acc.push(t); } else if (t.k === 'a') { metasOf(t.f, acc); metasOf(t.a, acc); }
  else if (t.k === 'l' || t.k === 'p') { metasOf(t.ty, acc); metasOf(t.b, acc); } else if (t.k === 'lg') metasOf(t.body, acc); return acc; };
const holeOf = t => { t = deref(t); if (t.k === 'm') return t; if (t.k === 'a') return holeOf(t.f) || holeOf(t.a); if (t.k === 'l' || t.k === 'p') return holeOf(t.ty) || holeOf(t.b); return null; };

function whnf(t) { for (;;) {
  t = deref(t);
  if (t.k === 'a') {
    const [h, sp] = spine(t), r = h.k === 'c' && G[h.n] && G[h.n].rec;
    if (r && sp.length >= r.arity) { // ι 化簡:遞迴子作用在建構子上
      const [mh, ma] = spine(whnf(sp[r.arity - 1])), c = mh.k === 'c' && r.ctors[mh.n];
      if (c) {
        const fields = ma.slice(r.np), pre = sp.slice(0, r.np + 1 + r.nc), rec = pre.reduce(A, C(h.n));
        let res = pre[r.np + 1 + c.idx]; fields.forEach(f => res = A(res, f));
        let T = G[mh.n].ty; ma.slice(0, r.np).forEach(p => { T = inst(deref(T).b, p); });
        fields.forEach((f, i) => { const Td = deref(T); if (c.recs[i]) res = A(res, A(spine(Td.ty)[1].slice(r.np).reduce(A, rec), f)); T = inst(Td.b, f); });
        sp.slice(r.arity).forEach(x => res = A(res, x)); t = res; continue;
      }
    }
    const f = whnf(t.f); if (f.k === 'l') { t = inst(f.b, t.a); continue; } return f === t.f ? t : A(f, t.a);
  }
  if (t.k === 'c' && G[t.n] && G[t.n].val) { t = G[t.n].val; continue; }
  return t;
} }
const nf = t => { t = whnf(t); if (t.k === 'a') return A(nf(t.f), nf(t.a));
  if (t.k === 'l' || t.k === 'p') { const x = FV(t.n, t.ty); return { ...t, ty: nf(t.ty), b: abs(nf(inst(t.b, x)), x) }; } return t; };

const undo = n => { while (trail.length > n) trail.pop().sol = null; };
const occurs = (m, t) => { t = deref(t); return t === m || (t.k === 'a' ? occurs(m, t.f) || occurs(m, t.a) : t.k === 'l' || t.k === 'p' ? occurs(m, t.ty) || occurs(m, t.b) : false); };
const assign = (m, t) => { if (occurs(m, t)) return false; m.sol = t; trail.push(m); return true; };
function defEq(a, b) { // 定義等價;遇到未解的洞就合一
  a = deref(a); b = deref(b); if (a === b) return true;
  if (a.k === 'm' && b.k === 'm' && a.hole && !b.hole) return assign(b, a);
  if (a.k === 'm') return assign(a, b); if (b.k === 'm') return assign(b, a);
  if (a.k === 'a' && b.k === 'a') {
    const [ha, xa] = spine(a), [hb2, xb] = spine(b);
    if (ha.k === 'c' && hb2.k === 'c' && ha.n === hb2.n && xa.length === xb.length) { const n = trail.length; if (xa.every((x, i) => defEq(x, xb[i]))) return true; undo(n); }
  }
  const a2 = whnf(a), b2 = whnf(b); if (a2 !== a || b2 !== b) return defEq(a2, b2);
  if (a.k !== b.k) return false;
  switch (a.k) {
    case 'f': return a.id === b.id; case 'c': return a.n === b.n; case 's': return a.l === b.l; case 'b': return a.i === b.i;
    case 'a': { if (spine(a)[0].k === 'm' || spine(b)[0].k === 'm') return false; return defEq(a.f, b.f) && defEq(a.a, b.a); }
    case 'l': case 'p': { if (!defEq(a.ty, b.ty)) return false; const x = FV(a.n, a.ty); return defEq(inst(a.b, x), inst(b.b, x)); }
  } return false;
}
const sortOf = T => { const s = whnf(infer(T)); if (s.k !== 's') die(`${show(T)} 不是型別(它的型別是 ${show(s)})`); return s.l; };
function infer(t) { t = deref(t);
  switch (t.k) {
    case 'f': return t.ty; case 's': return S(t.l + 1); case 'm': return t.ty || S(1);
    case 'z': FL.sorry = true; return t.ty;
    case 'c': { const d = G[t.n]; if (!d) die(`未定義的常數 ${t.n}`); return d.ty; }
    case 'p': { const s1 = sortOf(t.ty), x = FV(t.n, t.ty), s2 = sortOf(inst(t.b, x)); return S(s2 === 0 ? 0 : Math.max(s1, s2)); } // Prop 是 impredicative
    case 'l': { sortOf(t.ty); const x = FV(t.n, t.ty); return Pi(t.n, t.ty, abs(infer(inst(t.b, x)), x), t.imp); }
    case 'a': {
      const tf = whnf(infer(t.f)); if (tf.k !== 'p') die(`${show(t.f)} 不是函數,它的型別是 ${show(tf)}`);
      const ta = infer(t.a); if (!defEq(ta, tf.ty)) die(`型別不吻合:${show(t.a)} 的型別是 ${show(ta)},但這裡需要 ${show(tf.ty)}`);
      return inst(tf.b, t.a);
    }
  } die('內部錯誤:無法檢查這個項(' + t.k + ')');
}

/* ── 顯示 ── */
const par = (s, c) => c ? '(' + s + ')' : s;
const impFlags = ty => { const r = []; ty = deref(ty); while (ty.k === 'p') { r.push(!!ty.imp); ty = deref(ty.b); } return r; };
const natLit = t => { let n = 0; t = deref(t); while (t.k === 'a' && deref(t.f).k === 'c' && deref(t.f).n === 'Nat.succ') { n++; t = deref(t.a); } return t.k === 'c' && t.n === 'Nat.zero' ? n : -1; };
function show(t, ns = [], q = 0) { t = deref(t);
  switch (t.k) {
    case 'b': return ns[ns.length - 1 - t.i] ?? '#' + t.i;
    case 'f': return t.n; case 'm': return '?' + t.id; case 'z': return 'sorry'; case 'lg': return '⟨' + t.x.n + '⟩';
    case 'c': return t.n === 'Nat.zero' ? '0' : t.n;
    case 's': return t.l === 0 ? 'Prop' : t.l === 1 ? 'Type' : 'Type ' + (t.l - 1);
    case 'a': {
      const n = natLit(t); if (n >= 0) return '' + n;
      const [h, sp] = spine(t), ty = h.k === 'c' ? G[h.n] && G[h.n].ty : h.k === 'f' ? h.ty : null, fl = ty ? impFlags(ty) : [], as = sp.filter((_, i) => !fl[i]);
      if (h.k === 'c' && h.n === 'Eq' && as.length === 2) return par(show(as[0], ns, 2) + ' = ' + show(as[1], ns, 2), q > 1);
      if (h.k === 'c' && h.n === 'Nat.add' && as.length === 2) return par(show(as[0], ns, 3) + ' + ' + show(as[1], ns, 3), q > 2);
      return as.length ? par([show(h, ns, 3), ...as.map(x => show(x, ns, 3))].join(' '), q > 2) : show(h, ns, q);
    }
    case 'p': if (!t.imp && !usesB(t.b)) return par(show(t.ty, ns, 2) + ' → ' + show(t.b, [...ns, '_'], 1), q > 1);
    case 'l': { let n = t.n === '_' ? 'x' : t.n; while (ns.includes(n)) n += "'";
      const h = (t.imp ? '{' : '(') + n + ' : ' + show(t.ty, ns) + (t.imp ? '}' : ')'), b = show(t.b, [...ns, n]);
      return par(t.k === 'p' ? `∀ ${h}, ${b}` : `fun ${h} => ${b}`, q > 0); }
  } return '?';
}

/* ── 解析:產生有名字的語法樹 ── */
const tok = s => s.replace(/λ/g, ' fun ').replace(/[Π∀]/g, ' forall ').replace(/→/g, '->').replace(/⇒/g, '=>').match(/:=|->|=>|[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*|\d+|\S/g) || [];
const isId = x => x !== undefined && /^[A-Za-z_]/.test(x) && x !== 'fun' && x !== 'forall';
const isNum = x => /^\d+$/.test(x || '');
function P(src) {
  const T = tok(src); let p = 0;
  const peek = () => T[p], next = () => T[p++];
  const err = m => new MuError(`${m}(附近:${T.slice(Math.max(0, p - 3), p + 1).join(' ') || '結尾'})`);
  const expect = t => { if (T[p++] !== t) throw err(`語法錯誤:預期 "${t}"`); };
  const ident = () => { const x = T[p++]; if (!isId(x)) throw err('語法錯誤:這裡需要名稱'); return x; };
  const V = n => ({ k: 'var', n }), Ap = (f, a) => ({ k: 'app', f, a }), lit = n => n === 0 ? V('Nat.zero') : Ap(V('Nat.succ'), lit(n - 1));
  const wrap = (kind, bs, b) => bs.reduceRight((r, q) => ({ k: kind, n: q.n, ty: q.ty, imp: q.imp, b: r }), b);
  const atom = () => {
    const x = T[p++];
    if (x === '(') { const t = term(); if (T[p] === ':') { p++; const ty = term(); expect(')'); return { k: 'ann', e: t, ty }; } expect(')'); return t; }
    if (x === 'Prop') return { k: 'sort', l: 0 };
    if (x === 'Type') return isNum(T[p]) ? { k: 'sort', l: 1 + +T[p++] } : { k: 'sort', l: 1 };
    if (isNum(x)) return lit(+x);
    if (x === '_') return { k: 'hole' };
    if (!isId(x)) { p--; throw err('語法錯誤:這裡需要一個項'); }
    return V(x);
  };
  const app = () => { let t = atom(); while (p < T.length && (T[p] === '(' || isId(T[p]) || isNum(T[p]))) t = Ap(t, atom()); return t; };
  const add = () => { let l = app(); while (T[p] === '+') { p++; l = Ap(Ap(V('Nat.add'), l), app()); } return l; };
  const eq = () => { const l = add(); if (T[p] === '=') { p++; return Ap(Ap(V('Eq'), l), add()); } return l; };
  const arrow = () => { const l = eq(); if (T[p] !== '->') return l; p++; return { k: 'pi', n: '_', ty: l, imp: false, b: term() }; };
  const binders = () => { const bs = [];
    for (;;) { const x = T[p];
      if (x === '(' || x === '{') { p++; const ns = []; while (T[p] !== ':') ns.push(ident()); p++; const ty = term(); expect(x === '(' ? ')' : '}'); ns.forEach(n => bs.push({ n, ty, imp: x === '{' })); }
      else if (isId(x)) bs.push({ n: ident(), ty: null, imp: false });
      else return bs; } };
  const term = () => { const x = T[p];
    if (x === 'fun' || x === 'forall') {
      p++; const bs = binders(); if (T[p] === '=>' || T[p] === ',' || T[p] === '.') p++; else throw err('語法錯誤:binder 後需要 "=>"(fun)或 ","(forall)');
      return wrap(x === 'fun' ? 'lam' : 'pi', bs, term());
    }
    return arrow(); };
  return { term, binders, ident, expect, peek, next, err, wrap, done: () => p >= T.length };
}

/* ── ③ elaborator:語法樹 → 核心項;隱式參數、洞與合一 ── */
const lcOf = env => env.map(e => e.fv);
function ins(t, ty, env) { for (;;) { const T = whnf(ty); if (T.k === 'p' && T.imp) { const m = newMeta(T.ty, lcOf(env)); t = A(t, m); ty = inst(T.b, m); } else return [t, ty]; } }
const mismatch = (ty, exp) => die(`型別不吻合:\n  得到 ${show(zk(ty))}\n  需要 ${show(zk(exp))}`);
function elabType(e, env) { const [t, ty] = elab(e, env), s = whnf(ty); if (s.k !== 's' && s.k !== 'm') die(`${show(zk(t))} 不是型別(它的型別是 ${show(zk(ty))})`); return t; }
function elab(e, env, exp) { const r = elab1(e, env, exp); if (exp && !defEq(r[1], exp)) mismatch(r[1], exp); return r; }
function elab1(e, env, exp) {
  switch (e.k) {
    case 'sort': return [S(e.l), S(e.l + 1)];
    case 'hole': { const T = exp || newMeta(null, lcOf(env)), m = newMeta(T, lcOf(env)); m.hole = true; return [m, T]; }
    case 'var': {
      for (let i = env.length; i--; ) if (env[i].n === e.n) return ins(env[i].fv, env[i].fv.ty, env);
      if (!G[e.n]) die(`未定義的名稱 ${e.n}`);
      return ins(C(e.n), G[e.n].ty, env);
    }
    case 'ann': { const T = elabType(e.ty, env), [t] = elab(e.e, env, T); return [t, T]; }
    case 'lam': {
      const pe = exp && whnf(exp).k === 'p' ? whnf(exp) : null;
      const bt = e.ty ? elabType(e.ty, env) : pe ? pe.ty : newMeta(S(1), lcOf(env));
      if (pe && e.ty && !defEq(bt, pe.ty)) mismatch(bt, pe.ty);
      const x = FV(e.n, bt, e.imp), [b, bty] = elab(e.b, [...env, { n: e.n, fv: x }], pe ? inst(pe.b, x) : null);
      return [Lam(e.n, zk(bt), abs(zk(b), x), e.imp), Pi(e.n, zk(bt), abs(zk(bty), x), e.imp)];
    }
    case 'pi': {
      const bt = elabType(e.ty || { k: 'hole' }, env), x = FV(e.n, bt, e.imp), b = elabType(e.b, [...env, { n: e.n, fv: x }]);
      const t = Pi(e.n, zk(bt), abs(zk(b), x), e.imp); return [t, infer(t)];
    }
    case 'app': {
      const args = []; let h = e; while (h.k === 'app') { args.unshift(h.a); h = h.f; }
      const [t0, ty0] = elab(h, env), n0 = trail.length;
      if (exp) { // 先把期望型別傳進去(能讓 _ 與隱式參數更早被解出來);失敗就退回逐個參數處理
        try {
          let t = t0, ty = ty0; const ms = [];
          for (const _ of args) { [t, ty] = ins(t, ty, env); const T = whnf(ty); if (T.k !== 'p') throw 0; const m = newMeta(T.ty, lcOf(env)); ms.push(m); t = A(t, m); ty = inst(T.b, m); }
          [t, ty] = ins(t, ty, env);
          if (defEq(ty, exp)) { args.forEach((a, i) => { const [at] = elab(a, env, ms[i].ty); if (!defEq(ms[i], at)) mismatch(ms[i].ty, ms[i]); }); return [t, ty]; }
          undo(n0);
        } catch (x) { if (x instanceof MuError) throw x; undo(n0); }
      }
      let t = t0, ty = ty0;
      for (const a of args) {
        [t, ty] = ins(t, ty, env); const T = whnf(ty);
        if (T.k !== 'p') die(`${show(zk(t))} 不是函數(它的型別是 ${show(zk(ty))}),但被套用了參數`);
        const [at] = elab(a, env, T.ty); t = A(t, at); ty = inst(T.b, at);
      }
      return ins(t, ty, env);
    }
  } die('內部錯誤:未知的語法節點');
}
const noHoles = t => { const m = holeOf(t); if (m) die(`無法推出 _(它的型別是 ${m.ty ? show(zk(m.ty)) : '未知'}),請明確寫出`); };
function closedType(ast) { const t = zk(elabType(ast, [])); noHoles(t); infer(t); return t; }
function elabClosed(ast, exp) { const [t0] = elab(ast, [], exp), t = zk(t0); noHoles(t); if (!defEq(infer(t), exp)) mismatch(infer(t), exp); return t; }

/* ── ② 歸納型別:正向性檢查與遞迴子生成 ── */
function doInductive(q) {
  const name = q.ident(), bs = q.binders(); q.expect(':'); const sortAst = q.term(), ctors = [];
  while (q.peek() === '|') { q.next(); const cn = q.ident(); q.expect(':'); ctors.push({ cn, ty: q.term() }); }
  if (!q.done()) throw q.err('語法錯誤:多餘的符號');
  const env = [], ps = [];
  for (const b of bs) { const T = zk(elabType(b.ty, env)), x = FV(b.n, T, b.imp); ps.push(x); env.push({ n: b.n, fv: x }); }
  const peel = T => { const fs = []; let cur = T; for (;;) { cur = deref(cur); if (cur.k !== 'p') break; const x = FV(cur.n === '_' ? 'a' : cur.n, cur.ty, cur.imp); fs.push(x); cur = inst(cur.b, x); } return { fs, res: cur }; };
  const idxTy = zk(elabType(sortAst, env)), { fs: ix0, res: sres } = peel(idxTy), ni = ix0.length;  // 型別 = Π 索引, Sort
  if (deref(sres).k !== 's') die('歸納型別的結果必須是 Prop 或 Type(前面可以有索引的 Π)');
  const sl = deref(sres).l; G[name] = { ty: mkPi(ps, idxTy) };
  const sp = ps.map(x => x.imp), np = ps.length, base = ps.reduce((t, p) => A(t, p), C(name)), IPx = ixs => ixs.reduce((t, i) => A(t, i), base); ps.forEach(x => { x.imp = true; });
  const shapeOk = ty => { const [h, a] = spine(ty); return h.k === 'c' && h.n === name && a.length === np + ni && a.slice(0, np).every((y, i) => deref(y) === ps[i]) && !a.slice(np).some(j => mentions(j, name)); };
  const info = ctors.map((c, idx) => {
    const T = zk(elabType(c.ty, env)), { fs, res } = peel(T);
    if (!shapeOk(res)) die(`建構子 ${c.cn} 的結果必須是 ${name} 加上它的參數與索引(索引裡不能再提到 ${name})`);
    const recs = fs.map(f => {
      if (!mentions(f.ty, name)) { if (sl > 0 && sortOf(f.ty) > sl) die(`建構子 ${c.cn} 的欄位 ${f.n} 的宇宙層級太高(需要 ≤ ${show(S(sl))})`); return false; }
      if (!shapeOk(f.ty)) die(`建構子 ${c.cn} 的欄位 ${f.n} 不是嚴格正向的遞迴(目前只支援欄位型別正好是 ${name} 加參數與索引)`);
      return true;
    });
    const full = `${name}.${c.cn}`; G[full] = { ty: mkPi(ps, T), ctor: { I: name, idx } };
    const ridx = spine(res)[1].slice(np);
    return { full, T, nf: fs.length, recs, subOk: fs.every(f => sortOf(f.ty) === 0 || ridx.some(j => occF(j, f))) };
  });
  const order = info.map(c => c.full), cmap = {}; info.forEach((c, idx) => { cmap[c.full] = { idx, nf: c.nf, recs: c.recs }; });
  const subsingleton = sl === 0 && (info.length === 0 || (info.length === 1 && info[0].subOk)); // 零個建構子,或一個建構子且欄位都是證明/出現在索引裡 → 允許大消去
  for (const [rn, target] of [[name + '.ind', 0], ...(sl > 0 || subsingleton ? [[name + '.rec', 1]] : [])]) { // I.ind 目標 Prop(歸納法),I.rec 目標 Type(定義函數)
    const ix1 = peel(idxTy).fs, x1 = FV('x', IPx(ix1)), Cm = FV('motive', mkPi([...ix1, x1], S(target)));
    const capp = (js, x) => A(js.reduce((t, i) => A(t, i), Cm), x);
    const Ms = info.map(c => {
      const { fs, res } = peel(c.T); fs.forEach(f => { f.imp = false; });
      const ihs = fs.filter((_, i) => c.recs[i]).map(f => FV('ih', capp(spine(f.ty)[1].slice(np), f)));
      const ap = fs.reduce((t, f) => A(t, f), ps.reduce((t, p) => A(t, p), C(c.full)));
      return FV(c.full.split('.')[1], mkPi([...fs, ...ihs], capp(spine(res)[1].slice(np), ap)));
    });
    const ix2 = peel(idxTy).fs, X = FV('x', IPx(ix2)), ty = mkPi([...ps, Cm, ...Ms, ...ix2, X], capp(ix2, X));
    infer(ty); G[rn] = { ty, rec: { np, ni, nc: info.length, arity: np + 1 + info.length + ni + 1, order, ctors: cmap } };
  }
  ps.forEach((x, i) => { x.imp = sp[i]; });
  return `${name}(${info.map(c => c.full.split('.')[1]).join(' | ')})  ${name}.ind${sl > 0 || subsingleton ? ' ' + name + '.rec' : ''}`;
}

/* ── ④ 策略:目標是洞(meta);證明項的 lg 節點代表「這裡要 intro 一個變數」,最後再收尾成 λ ── */
const fin = t => { t = deref(t);
  switch (t.k) {
    case 'm': return die('還有未解決的目標 ?' + t.id);
    case 'lg': return Lam(t.x.n, zk(t.x.ty), abs(fin(t.body), t.x), t.x.imp);
    case 'a': return A(fin(t.f), fin(t.a));
    case 'l': case 'p': return { ...t, ty: fin(t.ty), b: fin(t.b) };
    default: return t;
  } };
const showGoal = g => [...g.lc.filter(x => !x.n.includes('#')).map(x => `${x.n} : ${show(x.ty)}`), '⊢ ' + show(g.ty)].join('\n');
const showGoals = gs => gs.length ? (gs.length > 1 ? gs.length + ' 個目標\n\n' : '') + gs.map(showGoal).join('\n\n') : '沒有目標了';

/* ── 索引合一:subst / injection / discriminate(cases 遇到非變數索引時自動使用) ── */
const mkGoal = (lc, ty) => { const m = newMeta(ty, lc); m.goal = true; return m; };
const SOLLOG = [];
const setG = (St, g, sol, gs = []) => { SOLLOG.push([g, g.sol]); g.sol = sol; St.goals = [...gs, ...St.goals.slice(1)]; };
const openGoals = (t, lc) => { const ms = metasOf(t), bad = ms.find(m => !m.hole);
  if (bad) die(`無法推出隱式參數(它的型別是 ${bad.ty ? show(zk(bad.ty)) : '未知'}),請明確寫出`); return ms.map(m => { m.goal = true; m.lc = lc; return m; }); };
function doApply(St, g, t, ty) { // 依賴型參數(∀)與前提都用洞補上,洞被合一解出就不再是目標
  const env = g.lc.map(x => ({ n: x.n, fv: x }));
  for (;;) {
    [t, ty] = ins(t, ty, env); const n = trail.length; if (defEq(ty, g.ty)) break; undo(n);
    const T = whnf(ty); if (T.k !== 'p') die(`apply 失敗:${show(zk(ty))} 的結論無法吻合目標 ${show(zk(g.ty))}`);
    const m = newMeta(T.ty, g.lc); m.hole = true; t = A(t, m); ty = inst(T.b, m);
  }
  setG(St, g, t, openGoals(t, g.lc));
}
const eqP = ty => { const [h, a] = spine(zk(ty)); return h.k === 'c' && h.n === 'Eq' && a.length === 3 ? a : null; };
const ctorView = t => { const [h, sp] = spine(whnf(t)), d = h.k === 'c' && G[h.n] && G[h.n].ctor; return d ? { name: h.n, I: d.I, args: sp } : null; };
const ctorNorm = t => { t = whnf(t); const [h, sp] = spine(t); return h.k === 'c' && G[h.n] && G[h.n].ctor ? sp.reduce((acc, x) => A(acc, ctorNorm(x)), h) : t; }; // 沿建構子結構化簡(n + 1 → succ n)
const lastBy = (lc, n) => [...lc].reverse().find(x => x.n === n);
function codeFn(I, params, T, body) { // λ x:T. I.rec params (λ_. Prop) (各建構子的 minor = λ 欄位. body) x —— 用遞迴子造出「Prop 值的編碼函數」
  const rd = G[I + '.rec']; if (!rd) die(`${I} 沒有 .rec(Prop 的歸納型別不支援 injection / discriminate)`);
  const r = rd.rec; if (r.ni) die(`${I} 有索引,injection / discriminate 目前只支援沒有索引的型別`);
  let rt = rd.ty; params.forEach(p => { rt = inst(deref(rt).b, p); });
  const motive = Lam('_', T, S(0)); rt = inst(deref(rt).b, motive); const minors = [];
  for (const cn of r.order) {
    const Td = deref(rt), c = r.ctors[cn], xs = []; let cur = Td.ty;
    while ((cur = deref(cur)).k === 'p') { const x = FV(cur.n === '_' ? 'a' : cur.n, cur.ty); xs.push(x); cur = inst(cur.b, x); }
    const m = mkLam(xs, body(cn, xs.slice(0, c.nf))); minors.push(m); rt = inst(Td.b, m);
  }
  const x = FV('x', T); let app = A(params.reduce(A, C(I + '.rec')), motive); minors.forEach(m => { app = A(app, m); });
  return Lam('x', T, abs(A(app, x), x));
}
function substVar(St, g, e, v, o, pe, Aty) { // 把區域變數 v 換成 o(pe : o = v)。依賴 v 的假設先收回目標,代換後再 intro
  const gt = zk(g.ty); if (occF(o, v)) die('subst 失敗:變數出現在等號另一邊(occurs check)');
  let sg = 0; try { sg = sortOf(gt); } catch (x) { /* 當作 Prop */ } if (sg > 1) die('目標的宇宙層級太高(只支援 Prop 與 Type 的目標)');
  const deps = []; for (const x of g.lc) { if (x === v || x === e) continue; if (occF(x.ty, v) || deps.some(d => occF(x.ty, d))) deps.push(x); }
  if (deps.some(d => occF(o, d))) die('subst 失敗:另一邊的項依賴於會被替換掉的假設');
  const Gd = mkPi(deps, gt), motive = Lam(v.n, zk(v.ty), abs(Lam('e', A(A(A(C('Eq'), Aty), o), v), Gd), v));
  let cur = hbs(A(A(motive, o), A(A(C('Eq.refl'), Aty), o))); const xs = [];
  for (let i = 0; i < deps.length; i++) { const T = deref(cur), x = FV(T.n, T.ty, T.imp); xs.push(x); cur = inst(T.b, x); }
  const ng = mkGoal([...g.lc.filter(x => x !== v && x !== e && !deps.includes(x)), ...xs], cur);
  const minor = xs.reduceRight((b, x) => ({ k: 'lg', x, body: b }), ng);
  let pf = A(A(A(A(A(A(C(sg > 0 ? 'Eq.rec' : 'Eq.ind'), Aty), o), motive), minor), v), pe); deps.forEach(d => { pf = A(pf, d); });
  setG(St, g, pf, [ng]);
}
function injectEq(St, g, e) { // c a = c b ⟹ a_j = b_j(只處理型別不依賴前面欄位的欄位)
  const a = eqP(e.ty); if (!a) die('injection 需要型別為 x = y 的假設');
  const [Aty, l, r] = a, cl = ctorView(l), cr = ctorView(r);
  if (!cl || !cr) die('injection:等號兩邊都必須是建構子的應用'); if (cl.name !== cr.name) die('injection:兩邊是不同的建構子(請用 discriminate)');
  const I = cl.I, np = G[I + '.ind'].rec.np, params = cl.args.slice(0, np), la = cl.args.slice(np), ra = cr.args.slice(np);
  let Tc = G[cl.name].ty; params.forEach(p => { Tc = inst(deref(Tc).b, p); }); let Tr = Tc; const xs = [], pfs = [];
  la.forEach((aj, j) => {
    const Td = deref(Tc), Tj = Td.ty;
    if (![...Array(j).keys()].some(k => usesB(deref(Tr).ty, k))) {
      const P = codeFn(I, params, Aty, (cn, fs) => cn === cl.name ? A(A(A(C('Eq'), Tj), aj), fs[j]) : C('True'));
      pfs.push(A(A(A(A(A(A(C('Eq.subst'), Aty), l), r), e), P), A(A(C('Eq.refl'), Tj), aj)));
      xs.push(FV(`${e.n}_${j + 1}`, A(A(A(C('Eq'), Tj), ctorNorm(aj)), ctorNorm(ra[j]))));
    }
    Tc = inst(Td.b, aj); Tr = deref(Tr).b;
  });
  if (!xs.length) die('injection:這個建構子沒有可以產生等式的欄位');
  const ng = mkGoal([...g.lc.filter(x => x !== e), ...xs], zk(g.ty));
  setG(St, g, xs.reduceRight((acc, x, i) => A({ k: 'lg', x, body: acc }, pfs[i]), ng), [ng]); return xs.map(x => x.n);
}
function discrEq(St, g, e) { // c a = d b(不同建構子)⟹ False,用編碼函數 c ↦ True、其餘 ↦ False
  const a = e && eqP(e.ty); if (!a) die('discriminate 需要型別為 x = y 的假設');
  const [Aty, l, r] = a, cl = ctorView(l), cr = ctorView(r);
  if (!cl || !cr || cl.I !== cr.I) die('discriminate:等號兩邊都必須是同一個歸納型別的建構子應用'); if (cl.name === cr.name) die('discriminate:兩邊是同一個建構子(請用 injection)');
  const params = cl.args.slice(0, G[cl.I + '.ind'].rec.np), Pd = codeFn(cl.I, params, Aty, cn => C(cn === cl.name ? 'True' : 'False'));
  const pfF = A(A(A(A(A(A(C('Eq.subst'), Aty), l), r), e), Pd), C('True.intro')); let sg = 0; try { sg = sortOf(g.ty); } catch (x) { /* 當作 Prop */ }
  setG(St, g, sg > 0 ? A(A(C('False.rec'), Lam('_', C('False'), zk(g.ty))), pfF) : A(A(C('False.elim'), zk(g.ty)), pfF));
}
function elimEq(St, e0) { // 化解一個等式假設:相同 → 略過;變數 → subst;同建構子 → injection 再遞迴;不同建構子 → discriminate
  const g = St.goals[0], e = g && lastBy(g.lc, e0.n), a = e && eqP(e.ty); if (!a) return;
  const [Aty, l0, r0] = a, l = ctorNorm(l0), r = ctorNorm(r0), lv = deref(l), rv = deref(r);
  if (defEq(l, r)) return;
  if (rv.k === 'f' && g.lc.includes(rv) && !occF(l, rv)) return substVar(St, g, e, rv, l, e, Aty);
  if (lv.k === 'f' && g.lc.includes(lv) && !occF(r, lv)) return substVar(St, g, e, lv, r, A(A(A(A(C('Eq.symm'), Aty), l), r), e), Aty);
  const cl = ctorView(l), cr = ctorView(r);
  if (cl && cr) { if (cl.name === cr.name) injectEq(St, g, e).forEach(n => elimEq(St, { n })); else discrEq(St, g, e); }
}

/* ── match:編譯成 cases(非遞迴)或 induction(結構遞迴),再逐分支 exact ── */
function parseMatch(text, x, fname, bs) {
  const explicit = bs.filter(b => !b.imp).map(b => b.n), branches = [];
  for (const part of text.split(/\n\s*\|/).map(p => p.replace(/^\s*\|/, '')).filter(p => p.trim())) {
    const m = part.match(/^\s*([\w.']+)((?:\s+[\w']+)*)\s*=>\s*([\s\S]*)$/); if (!m) die('match 分支格式:| 建構子 變數… => 項');
    branches.push({ ctor: m[1], vars: m[2].trim() ? m[2].trim().split(/\s+/) : [], rhs: m[3].trim() });
  }
  if (!branches.length) die('match 至少需要一個分支');
  const esc = fname.replace(/\./g, '\\.'), rec = branches.some(b => new RegExp('(^|[^\\w.])' + esc + "(?![\\w.'])").test(b.rhs));
  if (rec && explicit[explicit.length - 1] !== x) die('遞迴定義要求 match 的對象是最後一個明確參數');
  return { x, branches, rec, fname, explicit };
}
function rewriteRec(ast, sp, ihMap) { // f 固定參數… 遞迴欄位  ⟹  該欄位的 ih
  const E = sp.explicit.length, fixed = sp.explicit.slice(0, -1);
  const bad = () => die(`遞迴呼叫必須寫成 ${[sp.fname, ...fixed, '(遞迴欄位)'].join(' ')}(目前只支援結構遞迴)`);
  const go = t => {
    switch (t.k) {
      case 'app': {
        const args = []; let h = t; while (h.k === 'app') { args.unshift(h.a); h = h.f; }
        if (h.k === 'var' && h.n === sp.fname) {
          const last = args[E - 1];
          if (args.length === E && fixed.every((n, i) => args[i].k === 'var' && args[i].n === n) && last.k === 'var' && ihMap[last.n]) return { k: 'var', n: ihMap[last.n] };
          bad();
        }
        return args.reduce((f, x) => ({ k: 'app', f, a: go(x) }), go(h));
      }
      case 'var': if (t.n === sp.fname) bad(); return t;
      case 'lam': case 'pi': return { ...t, ty: t.ty && go(t.ty), b: go(t.b) };
      case 'ann': return { ...t, e: go(t.e), ty: go(t.ty) };
      default: return t;
    }
  };
  return go(ast);
}

/* ── 認證式自動化(不可信的搜尋):搜尋只決定「用哪些策略」,產生的證明項照常交給核心檢查 ──
   auto:直覺主義命題邏輯的完整證明搜尋(Dyckhoff 的 G4ip,可逆規則直接套用、不可逆規則才回溯)+ 一階的反向鏈結(合一)、∃ 見證搜尋、Eq。
   tauto:古典命題邏輯的判定程序——對原子命題用 Classical.em 分情況,葉節點交給 auto。 */
const save = St => ({ n: SOLLOG.length, t: trail.length, goals: St.goals });
const restore = (St, sv) => { while (SOLLOG.length > sv.n) { const [m, o] = SOLLOG.pop(); m.sol = o; } undo(sv.t); St.goals = sv.goals; };
const hv = () => 'h#' + (++hid);
function shape(t0) { // 把命題分類成 imp / all / and / or / ex / false / true / atom
  const t = hbs(zk(t0)), [h, sp] = spine(t), nm = h.k === 'c' ? h.n : '';
  if (h.k === 'p') return usesB(h.b) ? { k: 'all' } : { k: 'imp', a: h.ty, b: inst(h.b, h.ty) };
  if (nm === 'Not' && sp.length === 1) return { k: 'imp', a: sp[0], b: C('False') };
  if ((nm === 'And' || nm === 'Or') && sp.length === 2) return { k: nm === 'And' ? 'and' : 'or', a: sp[0], b: sp[1] };
  if (nm === 'Exists' && sp.length === 2) return { k: 'ex' };
  if (nm === 'False' && !sp.length) return { k: 'false' };
  if (nm === 'True' && !sp.length) return { k: 'true' };
  return { k: 'atom' };
}
function replaceHyp(St, old, news) { // 用推出來的新假設取代舊假設(新假設名稱隱藏);回傳新假設
  const g = St.goals[0], xs = news.map(n => FV(hv(), n.T)), ng = mkGoal([...g.lc.filter(y => y !== old), ...xs], g.ty);
  setG(St, g, xs.reduceRight((acc, x, i) => A({ k: 'lg', x, body: acc }, news[i].pf), ng), [ng]); return xs;
}
function invGoal(St) { // 目標端的可逆規則
  const s = shape(St.goals[0].ty);
  if (s.k === 'imp' || s.k === 'all') { tactic(St, 'intro', hv()); return true; }
  if (s.k === 'and' || s.k === 'true') { tactic(St, 'constructor', ''); return true; }
  return false;
}
function invHyp(St) { // 假設端的可逆規則
  const g = St.goals[0];
  for (const x of [...g.lc].reverse()) {
    const s = shape(x.ty), cs = names => tactic(St, 'cases', `${x.n} with ${names.join(' ')}`);
    if (s.k === 'false') { cs([]); return true; }
    if (s.k === 'and' || s.k === 'or' || s.k === 'ex') { cs([hv(), hv()]); return true; }
    if (s.k === 'true') { replaceHyp(St, x, []); return true; }
    if (s.k !== 'imp') continue;
    const sa = shape(s.a), B = s.b;
    if (sa.k === 'false') { replaceHyp(St, x, []); return true; }
    if (sa.k === 'true') { replaceHyp(St, x, [{ T: B, pf: A(x, C('True.intro')) }]); return true; }
    if (sa.k === 'and' || sa.k === 'or') { // (P∧Q)→B ⟹ P→Q→B;(P∨Q)→B ⟹ P→B 與 Q→B
      const [P, Q] = spine(hbs(zk(s.a)))[1], a = FV('a', P), b = FV('b', Q);
      if (sa.k === 'and') replaceHyp(St, x, [{ T: mkPi([a, b], B), pf: mkLam([a, b], A(x, A(A(A(A(C('And.intro'), P), Q), a), b))) }]);
      else replaceHyp(St, x, [{ T: mkPi([a], B), pf: mkLam([a], A(x, A(A(A(C('Or.inl'), P), Q), a))) }, { T: mkPi([b], B), pf: mkLam([b], A(x, A(A(A(C('Or.inr'), P), Q), b))) }]);
      return true;
    }
    const q = g.lc.find(y => y !== x && eqT(zk(y.ty), zk(s.a))); // 前提已經在假設裡:modus ponens
    if (q) { replaceHyp(St, x, [{ T: B, pf: A(x, q) }]); return true; }
  }
  return false;
}
function special(St, g, x, sx) { // G4ip 的 (C→D)→B 規則:先在 C 與 D→B 之下證明 D,再用 B 繼續
  const sa = shape(sx.a), Cc = sa.a, D = sa.b, B = sx.b, rest = g.lc.filter(y => y !== x);
  const c = FV(hv(), Cc), hDB = FV(hv(), Pi('_', D, B)), b = FV(hv(), B), d = FV('d', D);
  const g1 = mkGoal([...rest, c, hDB], D), g2 = mkGoal([...rest, b], zk(g.ty)), lamD = mkLam([d], A(x, mkLam([FV('_', Cc)], d)));
  setG(St, g, A({ k: 'lg', x: b, body: g2 }, A(x, { k: 'lg', x: c, body: A({ k: 'lg', x: hDB, body: g1 }, lamD) })), [g1, g2]);
}
const rankG = q => { try { return sortOf(q.ty) === 0 ? 0 : 1; } catch (x) { return 0; } }; // 證明目標先於資料目標(見證可由合一得到)
function solveAll(St, d) { const gs = [...St.goals].sort((p, q) => rankG(p) - rankG(q)); St.goals = []; return gs.every(q => q.sol || prove(q, d)); }
function attempt(St, d, fn) { const sv = save(St); try { fn(); if (solveAll(St, d)) return true; } catch (e) { if (!(e instanceof MuError)) throw e; } restore(St, sv); return false; }
function prove(g, d) { return g.sol ? true : step({ goals: [g] }, d); }
function step(St, d) {
  for (;;) {
    if (!St.goals.length) return true;
    if (St.goals.length > 1) return solveAll(St, d);
    const g = St.goals[0]; if (g.sol) return true; g.ty = hbs(zk(g.ty));
    if (invGoal(St) || invHyp(St)) continue;
    return branches(St, d);
  }
}
function branches(St, d) { // 不可逆的選擇:每次選擇都要回溯,深度減一
  if (d <= 0) return false;
  const g = St.goals[0], s = shape(g.ty), at = fn => attempt(St, d - 1, fn), rev = [...g.lc].reverse();
  for (const x of rev) if (at(() => { if (!defEq(x.ty, g.ty)) die('不吻合'); setG(St, g, x); })) return true;
  if (s.k === 'or') for (const side of ['left', 'right']) if (at(() => tactic(St, side, ''))) return true;
  if (s.k === 'ex' && at(() => tactic(St, 'refine', 'Exists.intro _ _'))) return true;
  if (at(() => tactic(St, 'rfl', ''))) return true;
  for (const x of rev) {
    const sx = shape(x.ty);
    if ((sx.k === 'imp' || sx.k === 'all') && at(() => doApply(St, g, x, x.ty))) return true;
    if (sx.k === 'imp' && shape(sx.a).k === 'imp' && at(() => special(St, g, x, sx))) return true;
  }
  return at(() => tactic(St, 'symm', ''));
}
const dedupe = lc => { for (let i = 0; i < lc.length; i++) while (lc.slice(i + 1).some(y => y.n === lc[i].n)) lc[i].n += "'"; };

function tactic(St, name, arg) {
  const g = St.goals[0]; if (!g) die('已經沒有目標了');
  const ws = arg.trim() ? arg.trim().split(/\s+/) : [], env = g.lc.map(x => ({ n: x.n, fv: x })), gty = () => zk(g.ty);
  const mkG = (lc, ty) => { const m = newMeta(ty, lc); m.goal = true; return m; };
  const set = (sol, gs = []) => setG(St, g, sol, gs);
  const el = (src, exp) => { const q = P(src), t = q.term(); if (!q.done()) throw q.err('語法錯誤:多餘的符號'); return elab(t, env, exp); };
  const open = t => openGoals(t, g.lc);
  const eqParts = ty => { const [h, a] = spine(zk(ty)); return h.k === 'c' && h.n === 'Eq' && a.length === 3 ? a : null; };
  switch (name) {
    case 'intro': {
      if (ws.length > 1) return ws.forEach(w => tactic(St, 'intro', w));
      const T = whnf(gty()); if (T.k !== 'p') die(`intro 失敗:目標 ${show(g.ty)} 不是 → 或 ∀`);
      const n = ws[0] || (T.n === '_' ? 'h' : T.n), x = FV(n, T.ty, T.imp), ng = mkG([...g.lc, x], inst(T.b, x));
      return set({ k: 'lg', x, body: ng }, [ng]);
    }
    case 'exact': { const [t] = el(arg, g.ty); if (open(t).length) die('exact 裡不能留下 _(要留下目標請用 refine)'); return set(t); }
    case 'refine': { const [t] = el(arg, g.ty); return set(t, open(t)); }
    case 'apply': { const [t0, ty0] = el(arg); return doApply(St, g, t0, ty0); }
    case 'assumption': { for (let i = g.lc.length; i--; ) { const n = trail.length; if (defEq(g.lc[i].ty, g.ty)) return set(g.lc[i]); undo(n); } die('找不到符合目標的假設'); }
    case 'have': {
      const i = arg.indexOf(':='), lhs = i < 0 ? arg : arg.slice(0, i), j = lhs.indexOf(':'); if (j < 0) die('格式:have 名稱 : 命題 [:= 項]');
      const n = lhs.slice(0, j).trim(), q = P(lhs.slice(j + 1)), T = zk(elabType(q.term(), env)), x = FV(n, T);
      if (i >= 0) { const [t] = el(arg.slice(i + 2), T), ng = mkG([...g.lc, x], g.ty); return set(A({ k: 'lg', x, body: ng }, t), [ng]); }
      const g1 = mkG(g.lc, T), g2 = mkG([...g.lc, x], g.ty); return set(A({ k: 'lg', x, body: g2 }, g1), [g1, g2]);
    }
    case 'rfl': {
      const a = eqParts(g.ty); if (!a) die('rfl 只適用於 x = y 型的目標');
      if (!defEq(a[1], a[2])) die(`rfl 失敗:${show(a[1])} 與 ${show(a[2])} 並非定義等價`); return set(A(A(C('Eq.refl'), a[0]), a[1]));
    }
    case 'symm': {
      const a = eqParts(g.ty); if (!a) die('symm 只適用於 x = y 型的目標');
      const ng = mkG(g.lc, A(A(A(C('Eq'), a[0]), a[2]), a[1])); return set(A(A(A(A(C('Eq.symm'), a[0]), a[2]), a[1]), ng), [ng]);
    }
    case 'rw': { // rw h:把目標中的 a 換成 b;rw ← h:把 b 換成 a(h : a = b)
      const rev = ws[0] === '←' || ws[0] === '<-', [t, ty] = el(rev ? arg.trim().slice(ws[0].length) : arg), a = eqParts(ty);
      if (!a) die('rw 需要型別為 x = y 的假設');
      const [l, r] = rev ? [a[2], a[1]] : [a[1], a[2]], body = absT(gty(), l);
      if (!usesB(body)) die(`rw 失敗:目標裡找不到 ${show(l)}`);
      const ng = mkG(g.lc, inst(body, r)), mot = Lam('z', a[0], body), esub = (x, y, hh) => A(A(A(A(A(C('Eq.subst'), a[0]), x), y), hh), mot); // Eq.subst x y h P : P x → P y
      return set(A(rev ? esub(a[1], a[2], t) : esub(a[2], a[1], A(A(A(A(C('Eq.symm'), a[0]), a[1]), a[2]), t)), ng), [ng]);
    }
    case 'auto': {
      const d = +ws[0] || 6, sv = save(St); dedupe(g.lc);
      if (!prove(g, d)) { restore(St, sv); die(`auto 找不到證明(搜尋深度 ${d})。可以拆解目標、先 have 需要的引理,或加大深度:auto ${d + 4}`); }
      St.goals = St.goals.slice(1); return;
    }
    case 'tauto': { // 古典命題邏輯:對每個原子命題 p 用 Classical.em 分成 p / ¬p 兩種情況,葉節點交給 auto
      if (!G['Classical.em']) die('tauto 需要公理 Classical.em'); const d = +ws[0] || 6, sv = save(St); dedupe(g.lc);
      const atoms = [], scan = t => { const sh = shape(t); if (sh.k === 'imp' || sh.k === 'and' || sh.k === 'or') { scan(sh.a); scan(sh.b); } else if (sh.k !== 'false' && sh.k !== 'true') { const z = zk(t); if (!atoms.some(a => eqT(a, z))) atoms.push(z); } };
      try { if (sortOf(g.ty) !== 0) die('tauto 的目標必須是命題'); scan(g.ty); g.lc.forEach(x => { try { if (sortOf(x.ty) === 0) scan(x.ty); } catch (e) { /* 不是命題 */ } }); } catch (e) { if (!(e instanceof MuError)) throw e; die('tauto 的目標必須是命題'); }
      if (atoms.length > 7) die(`原子命題太多(${atoms.length} > 7)`);
      const rec = (q, i) => {
        if (i === atoms.length) return prove(q, d);
        const S2 = { goals: [q] }, p = atoms[i], [e] = replaceHyp(S2, null, [{ T: A(A(C('Or'), p), A(C('Not'), p)), pf: A(C('Classical.em'), p) }]);
        tactic(S2, 'cases', `${e.n} with ${hv()} ${hv()}`); return S2.goals.every(q2 => rec(q2, i + 1));
      };
      if (!rec(g, 0)) { restore(St, sv); die('tauto 找不到證明:這個命題不是古典命題邏輯的重言式(或需要一階推理)'); }
      St.goals = St.goals.slice(1); return;
    }
    case 'match': {
      const sp = St.spec, h = lastBy(g.lc, sp.x); if (!h) die(`找不到變數 ${sp.x}`);
      let hty = zk(h.ty), [I] = spine(hty); if (I.k !== 'c') { hty = whnf(hty); [I] = spine(hty); }
      const rd = I.k === 'c' && G[I.n + '.ind']; if (!rd) die(`${sp.x} 的型別不是歸納型別`);
      const r = rd.rec, byCtor = {}, ihOf = {}, names = [];
      for (const b of sp.branches) { const full = r.order.find(cn => cn === b.ctor || cn === I.n + '.' + b.ctor); if (!full) die(`${b.ctor} 不是 ${I.n} 的建構子`); if (byCtor[full]) die(`建構子 ${full} 的分支重複了`); byCtor[full] = b; }
      for (const cn of r.order) { // 依建構子順序決定欄位名稱:隱式欄位用隱藏名稱,明確欄位用 pattern 的變數
        const c = r.ctors[cn], b = byCtor[cn], fn = []; let T = G[cn].ty, k = 0; ihOf[cn] = {};
        for (let i = 0; i < r.np; i++) T = deref(T).b;
        for (let i = 0; i < c.nf; i++) { T = deref(T); if (T.imp) fn.push(`${T.n}#`); else { const v = b ? b.vars[k++] : undefined; fn.push(v && v !== '_' ? v : 'a#'); } T = T.b; }
        if (b && k !== b.vars.length) die(`建構子 ${cn} 有 ${k} 個明確欄位,但分支寫了 ${b.vars.length} 個變數`);
        names.push(...fn); if (sp.rec) c.recs.forEach((rc, i) => { if (rc) { names.push(`ih_${fn[i]}`); ihOf[cn][fn[i]] = `ih_${fn[i]}`; } });
      }
      tactic(St, sp.rec ? 'induction' : 'cases', `${sp.x} with ${names.join(' ')}`);
      const mine = St.goals.filter(q => q.ctor), seen = new Set(mine.map(q => q.ctor));
      for (const cn of Object.keys(byCtor)) if (!seen.has(cn)) die(`分支 ${cn} 不可能發生(它的索引與目標不吻合,已被排除)`);
      for (const q of mine) {
        const b = byCtor[q.ctor]; if (!b) die(`缺少分支:${q.ctor}`);
        const qq = P(b.rhs); let ast = qq.term(); if (!qq.done()) throw qq.err('語法錯誤:多餘的符號');
        if (sp.rec) ast = rewriteRec(ast, sp, ihOf[q.ctor]);
        const [t] = elab(ast, q.lc.map(x => ({ n: x.n, fv: x })), q.ty);
        if (metasOf(zk(t)).length) die(`分支 ${q.ctor} 裡不能留下 _`);
        q.sol = t;
      }
      St.goals = St.goals.filter(q => !q.ctor); return;
    }
    case 'subst': {
      const e = lastBy(g.lc, ws[0]); if (!e) die(`找不到假設 ${ws[0]}`); const a = eqParts(e.ty); if (!a) die('subst 需要 x = y 型的假設');
      const [Aty, l, r] = a, rv = deref(r), lv = deref(l);
      if (rv.k === 'f' && g.lc.includes(rv)) return substVar(St, g, e, rv, l, e, Aty);
      if (lv.k === 'f' && g.lc.includes(lv)) return substVar(St, g, e, lv, r, A(A(A(A(C('Eq.symm'), Aty), l), r), e), Aty);
      die('subst 需要等號的一邊是區域變數');
    }
    case 'injection': { const e = lastBy(g.lc, ws[0]); if (!e) die(`找不到假設 ${ws[0]}`); injectEq(St, g, e); return; }
    case 'discriminate': case 'contradiction': { const e = lastBy(g.lc, ws[0]); if (!e) die(`找不到假設 ${ws[0]}`); return discrEq(St, g, e); }
    case 'induction': case 'cases': { // 通用:用 I.ind 對區域假設做歸納 / 分類討論。cases 的索引可以是任意項(自動做索引合一);依賴被分析對象的假設會自動收回再 intro
      const w = ws.filter(x => x !== 'with'), hn = w.shift(), h = lastBy(g.lc, hn); if (!h) die(`找不到假設 ${hn}`);
      let hty = zk(h.ty), [I, ps] = spine(hty); if (I.k !== 'c') { hty = whnf(hty); [I, ps] = spine(hty); }
      let sg = 0; try { sg = sortOf(gty()); } catch (x) { /* 當作 Prop */ } if (sg > 1) die('cases / induction 目前只支援目標在 Prop 或 Type 的情況');
      const rd = I.k === 'c' && G[I.n + (sg > 0 ? '.rec' : '.ind')];
      if (!rd) die(I.k === 'c' && G[I.n + '.ind'] ? `${I.n} 是 Prop 的歸納型別,不能對 Type 的目標做分類討論(沒有大消去)` : `${hn} 的型別 ${show(h.ty)} 不是歸納型別`);
      const r = rd.rec, params = ps.slice(0, r.np), idxArgs = ps.slice(r.np).map(deref);
      const isVar = idxArgs.map((x, i) => x.k === 'f' && g.lc.includes(x) && idxArgs.findIndex(y => y === x) === i && !params.some(p => occF(p, x)));
      if (name === 'induction' && !isVar.every(Boolean)) die('induction 目前只支援索引是變數的情況(cases 支援任意索引)');
      const ixs = idxArgs.map((x, i) => isVar[i] ? x : FV('i', zk(infer(x)))), Es = [];
      idxArgs.forEach((x, i) => { if (!isVar[i]) Es.push(FV('e', A(A(A(C('Eq'), ixs[i].ty), x), ixs[i]))); });
      const vfs = ixs.filter((_, i) => isVar[i]), deps = [];
      for (const x of g.lc) { if (x === h) continue; if ([h, ...vfs].some(b => occF(x.ty, b)) || deps.some(d => occF(x.ty, d))) deps.push(x); }
      const repl = (t, from, to) => { t = deref(t); return eqT(t, from) ? to : t.k === 'a' ? A(repl(t.f, from, to), repl(t.a, from, to)) : t.k === 'l' || t.k === 'p' ? { ...t, ty: repl(t.ty, from, to), b: repl(t.b, from, to) } : t; };
      let Gs = mkPi(deps, gty()); idxArgs.forEach((x, i) => { if (!isVar[i]) Gs = repl(Gs, x, ixs[i]); }); // 目標與依賴假設裡出現的索引項,一併換成新變數(像 generalize)
      let motive = Lam(h.n, ixs.reduce((t, i) => A(t, i), params.reduce(A, C(I.n))), abs(mkPi(Es, Gs), h));
      for (let i = ixs.length; i--; ) motive = Lam(ixs[i].n, zk(ixs[i].ty), abs(motive, ixs[i]));
      let T = rd.ty; params.forEach(p => { T = inst(deref(T).b, p); }); T = inst(deref(T).b, motive);
      const lcBase = g.lc.filter(x => x !== h && !deps.includes(x) && !vfs.includes(x)), gs = [], minors = [];
      const solveMinor = gM => { // 引入索引等式並化解,再把收回的假設 intro 回來
        const St2 = { goals: [gM] };
        for (let i = 0; i < Es.length && St2.goals.length; i++) { tactic(St2, 'intro', 'e'); elimEq(St2, { n: 'e' }); }
        for (let i = 0; i < deps.length && St2.goals.length; i++) tactic(St2, 'intro', deps[i].n);
        return St2.goals;
      };
      for (const cn of r.order) {
        const Td = deref(T), c = r.ctors[cn], xs = []; let cur = Td.ty, bi = 0;
        while ((cur = deref(cur)).k === 'p') {
          const isIh = bi++ >= c.nf, nm = isIh && name === 'cases' ? 'ih#' + (++hid) : w.length ? w.shift() : isIh ? 'ih' : cur.n === '_' ? 'a' : cur.n;
          const x = FV(nm, cur.ty); xs.push(x); cur = inst(cur.b, x);
        }
        const gM = mkG([...lcBase, ...xs], hbs(cur)), mp = xs.reduceRight((b, x) => ({ k: 'lg', x, body: b }), gM); minors.push(mp); T = inst(Td.b, mp);
        const outs = Es.length || deps.length ? solveMinor(gM) : [gM]; outs.forEach(q => { q.ctor = cn; }); gs.push(...outs);
      }
      let pf = params.reduce(A, C(I.n + (sg > 0 ? '.rec' : '.ind'))); pf = A(pf, motive); minors.forEach(m => { pf = A(pf, m); }); idxArgs.forEach(i => { pf = A(pf, i); }); pf = A(pf, h);
      idxArgs.forEach((x, i) => { if (!isVar[i]) pf = A(pf, A(A(C('Eq.refl'), ixs[i].ty), x)); }); deps.forEach(d => { pf = A(pf, d); });
      return set(pf, gs);
    }
    case 'constructor': case 'left': case 'right': {
      const [I] = spine(gty()), rd = I.k === 'c' && G[I.n + '.ind']; if (!rd) die(`${name} 只適用於目標是歸納型別的情況`);
      const order = rd.rec.order, cand = name === 'constructor' ? order : [order[name === 'left' ? 0 : 1]];
      for (const cn of cand) { if (!cn) break; const n = trail.length, s0 = St.goals; try { return tactic(St, 'apply', cn); } catch (x) { undo(n); St.goals = s0; } }
      die(`${name} 失敗:沒有建構子的結論吻合目標 ${show(gty())}`);
    }
    case 'exists': return tactic(St, 'refine', `Exists.intro (${arg}) _`);
    case 'exfalso': return tactic(St, 'apply', 'False.elim');
    case 'norm': { const ng = mkG(g.lc, nf(gty())); return set(ng, [ng]); }
    case 'sorry': return set({ k: 'z', ty: gty() });
  }
  die(`未知的策略 ${name}`);
}

/* ── ⑤ 指令與腳本 ── */
const PRELUDE = `inductive False : Prop
inductive True : Prop
  | intro : True
inductive And (A B : Prop) : Prop
  | intro : A -> B -> And A B
inductive Or (A B : Prop) : Prop
  | inl : A -> Or A B
  | inr : B -> Or A B
inductive Exists {A : Type} (P : A -> Prop) : Prop
  | intro : forall (x : A), P x -> Exists P
inductive Nat : Type
  | zero : Nat
  | succ : Nat -> Nat
inductive List (A : Type) : Type
  | nil : List A
  | cons : A -> List A -> List A
def Not (A : Prop) : Prop := A -> False
axiom Classical.em (P : Prop) : Or P (Not P)
inductive Eq {A : Type} (a : A) : A -> Prop
  | refl : Eq a a
def Eq.symm {A : Type} {x y : A} (h : x = y) : y = x := by
  cases h
  rfl
def Eq.trans {A : Type} {x y z : A} (h1 : x = y) (h2 : y = z) : x = z := by
  cases h2
  exact h1
def Eq.congr {A B : Type} (f : A -> B) {x y : A} (h : x = y) : f x = f y := by
  cases h
  rfl
def Eq.subst {A : Type} {a b : A} (h : a = b) (P : A -> Prop) (pa : P a) : P b := by
  cases h
  exact pa
theorem False.elim {C : Prop} (h : False) : C := by
  cases h
def Nat.add (m n : Nat) : Nat := Nat.rec (fun (_ : Nat) => Nat) m (fun (k : Nat) (r : Nat) => Nat.succ r) n
`;

const constsOf = (t, acc = new Set()) => { t = deref(t); if (t.k === 'c') acc.add(t.n); else if (t.k === 'a') { constsOf(t.f, acc); constsOf(t.a, acc); } else if (t.k === 'l' || t.k === 'p') { constsOf(t.ty, acc); constsOf(t.b, acc); } return acc; };
function recordAx(name, t, cmd, sorry) { // 這個定義/定理依賴哪些公理(含它用到的定理所依賴的公理)
  const out = new Set(sorry ? ['sorry'] : []);
  for (const c of constsOf(t)) { const d = G[c]; if (!d) continue; if (d.axiom) out.add(c); (d.axioms || []).forEach(a => out.add(a)); }
  G[name].axioms = [...out]; cmd.axioms = [...out]; cmd.cert = show(t).slice(0, 4000); // 證明項就是 certificate:任何人都能拿去重新檢查
}
function exec(text, R) {
  const L = text.split('\n').map(l => l.replace(/--.*$/, '')); R.lines = L;
  const starts = []; L.forEach((l, i) => /^(def|theorem|axiom|inductive|check|eval)\b/.test(l) && starts.push(i));
  starts.forEach((s, c) => {
    const e = c + 1 < starts.length ? starts[c + 1] : L.length, kind = L[s].trim().match(/^\w+/)[0], cmd = { kind, line: s, end: e, status: 'ok', text: '', msg: null, errLine: null };
    R.cmds.push(cmd);
    try {
      const body = L.slice(s, e).join(' ').trim().slice(kind.length).trim();
      if (kind === 'inductive') cmd.text = doInductive(P(body));
      else if (kind === 'check' || kind === 'eval') {
        const q = P(body), ast = q.term(); if (!q.done()) throw q.err('語法錯誤:多餘的符號');
        const [t0] = ast.k === 'var' && G[ast.n] ? [C(ast.n)] : elab(ast, []), t = zk(t0); noHoles(t); const ty = infer(t); cmd.text = `${show(kind === 'eval' ? nf(t) : t)} : ${show(ty)}`;
      } else if (kind === 'theorem' || (kind === 'def' && (L.slice(s, e).some(l => /:=\s*by(\s|$)/.test(l)) || /:=\s*match\s+[\w']+\s+with\b/.test(L.slice(s, e).join('\n'))))) theorem(L, s, e, cmd, R, kind === 'def');
      else { // def / axiom
        const q = P(body), name = q.ident(), bs = q.binders(); q.expect(':'); const tyAst = q.term(), ty = closedType(q.wrap('pi', bs, tyAst));
        if (kind === 'def') { q.expect(':='); FL.sorry = false; const val = elabClosed(q.wrap('lam', bs, q.term()), ty); if (!q.done()) throw q.err('語法錯誤:多餘的符號'); G[name] = { ty, val }; recordAx(name, val, cmd, FL.sorry); }
        else { if (!q.done()) throw q.err('語法錯誤:多餘的符號'); G[name] = { ty, axiom: true }; }
        cmd.text = `${name} : ${show(ty)}`;
      }
      if (!cmd.tac) for (let i = s; i < e; i++) R.info[i] = cmd.text;
    } catch (x) { cmd.status = 'error'; cmd.msg = x.message; R.errors[s] = x.message; }
  });
}
function theorem(L, s, e, cmd, R, isDef) {
  const joined = L.slice(s, e).join('\n'), mt = joined.match(/:=\s*match\s+([\w']+)\s+with\b/);
  let h = s; while (h < e && !/:=\s*by(\s|$)/.test(L[h])) h++;
  const hEnd = mt ? s + joined.slice(0, mt.index).split('\n').length - 1 : h;
  cmd.tac = true; const tac = !mt && h < e, q = P((mt ? joined.slice(0, mt.index) + ':=' : L.slice(s, tac ? h + 1 : e).join(' ')).trim().slice(isDef ? 3 : 7)), name = q.ident(), bs = q.binders(); q.expect(':');
  const tyAst = q.term(); q.expect(':='); const decl = closedType(q.wrap('pi', bs, tyAst)); cmd.text = `${name} : ${show(decl)}`;
  if (!tac && !mt) { FL.sorry = false; const tv = elabClosed(q.wrap('lam', bs, q.term()), decl); if (!q.done()) throw q.err('語法錯誤:多餘的符號'); G[name] = { ty: decl }; if (FL.sorry) cmd.status = 'sorry'; recordAx(name, tv, cmd, FL.sorry); return; }
  let ty = decl; const fvs = [];
  for (let i = 0; i < bs.length; i++) { const T = deref(ty), x = FV(T.n, T.ty, T.imp); fvs.push(x); ty = inst(T.b, x); }
  const root = newMeta(ty, fvs); root.goal = true; const St = { goals: [root] }; let failed = false;
  for (let i = s; i <= hEnd; i++) R.states[i] = showGoals(St.goals);
  const inline = tac && (L[h].match(/:=\s*by\s+(\S.*)$/) || [])[1]; // 單行寫法:theorem … := by auto
  for (let i = inline ? h : h + 1; i < e; i++) {
    const t = (i === h ? inline : L[i]).trim().replace(/^[·•*-]\s+/, '');
    if (t && !failed) try { const m = t.match(/^(\w+)\s*(.*)$/); if (!m) die('看不懂這一行'); tactic(St, m[1], m[2]); }
      catch (x) { failed = true; cmd.status = 'error'; cmd.msg = `第 ${i + 1} 行:${x.message}`; cmd.errLine = i; R.errors[i] = x.message; }
    R.states[i] = showGoals(St.goals);
  }
  if (mt) {
    try { St.spec = parseMatch(joined.slice(mt.index + mt[0].length), mt[1], name, bs); tactic(St, 'match', ''); }
    catch (x) { failed = true; const ml = L.findIndex((l, i) => i >= s && /\bmatch\b/.test(l)); cmd.status = 'error'; cmd.msg = `match:${x.message}`; cmd.errLine = ml; R.errors[ml] = x.message; }
    for (let i = hEnd + 1; i < e; i++) R.states[i] = showGoals(St.goals);
  }
  G[name] = { ty: decl };
  if (failed) return;
  if (St.goals.length) { cmd.status = 'open'; cmd.msg = `還有 ${St.goals.length} 個目標未完成`; return; }
  FL.sorry = false; const pf = mkLam(fvs, fin(root)); noHoles(pf);
  if (!defEq(infer(pf), decl)) die('核心推出的型別與宣告不符'); // 策略不可信,最後一律由核心重新檢查
  if (FL.sorry) cmd.status = 'sorry'; else if (isDef) G[name] = { ty: decl, val: pf }; // def 用策略寫:證明項成為可展開的定義
  recordAx(name, pf, cmd, FL.sorry);
}
function runScript(text) {
  G = {}; MS = []; trail = []; hid = 0; FL.sorry = false; SOLLOG.length = 0;
  const pre = { cmds: [], states: {}, info: {}, errors: {}, lines: [] }; exec(PRELUDE, pre);
  const bad = pre.cmds.find(c => c.status !== 'ok'); if (bad) die('內部錯誤:prelude 載入失敗:' + bad.msg);
  const R = { cmds: [], states: {}, info: {}, errors: {}, lines: [] }; exec(text, R); R.ok = R.cmds.every(c => c.status === 'ok'); R.size = Object.keys(G).length; return R;
}
const ICON = { ok: '✔', sorry: '⚠', open: '…', error: '✘' };
function report(R, trace, cert) {
  const ind = (s, k) => s.split('\n').map(x => ' '.repeat(k) + x), o = [];
  for (const c of R.cmds) {
    o.push(`${ICON[c.status]} ${c.kind} ${c.text}`.trimEnd());
    if (trace && c.kind === 'theorem') for (let i = c.line + 1; i < c.end; i++) if (R.lines[i].trim() && R.states[i] !== undefined && !(i in R.errors)) o.push('    ' + R.lines[i].trim(), ...ind(R.states[i], 8));
    if (c.axioms && c.axioms.length) o.push(`    依賴公理:${c.axioms.join(', ')}`);
    if (cert && c.cert && c.status !== 'error') o.push('    證明項:' + c.cert);
    if (c.msg) o.push(...ind(c.msg, 4));
    if (c.errLine !== null) o.push(...ind(R.states[c.errLine], 6));
    if (c.status === 'open') o.push(...ind(R.states[c.end - 1], 6));
  }
  return o.join('\n');
}

const examples = [
  { name: '宇宙階層與型別', src: 'check Type\ncheck Type 1\ncheck List Nat\ncheck Nat.succ\ncheck Eq.symm\neval 2 + 3\ncheck Nat.rec' },
  { name: '∧ 交換(cases)', src: 'theorem and_comm {A B : Prop} (h : And A B) : And B A := by\n  cases h with a b\n  exact And.intro b a' },
  { name: '∨ 交換', src: 'theorem or_comm {A B : Prop} (h : Or A B) : Or B A := by\n  cases h with a b\n  right\n  exact a\n  left\n  exact b' },
  { name: '存在量詞', src: 'theorem ex_swap {A : Type} {P Q : A -> Prop} (h : Exists (fun (x : A) => And (P x) (Q x))) : Exists (fun (x : A) => And (Q x) (P x)) := by\n  cases h with w hw\n  cases hw with hp hq\n  exact Exists.intro w (And.intro hq hp)' },
  { name: '歸納法:0 + n = n', src: 'theorem zero_add (n : Nat) : 0 + n = n := by\n  induction n with k ih\n  rfl\n  exact Eq.congr Nat.succ ih' },
  { name: 'List:append xs nil = xs', src: 'def List.append {A : Type} (xs ys : List A) : List A :=\n  List.rec (fun (_ : List A) => List A) ys (fun (x : A) (t : List A) (r : List A) => List.cons x r) xs\ntheorem append_nil {A : Type} (xs : List A) : List.append xs List.nil = xs := by\n  induction xs with x t ih\n  rfl\n  exact Eq.congr (List.cons x) ih' },
  { name: 'rw 改寫', src: 'theorem rw_demo {A : Type} (f : A -> A) {a b : A} (h : a = b) (Q : A -> Prop) (hq : Q (f b)) : Q (f a) := by\n  rw h\n  assumption' },
  { name: 'Eq 是歸納族(J 規則)', src: 'check Eq\ncheck Eq.refl\ncheck Eq.ind\ntheorem eq_symm2 {A : Type} {x y : A} (h : x = y) : y = x := by\n  cases h\n  rfl\ntheorem eq_trans2 {A : Type} {x y z : A} (h1 : x = y) (h2 : y = z) : x = z := by\n  cases h2\n  exact h1' },
  { name: 'Vec 與 Fin(歸納族)', src: 'inductive Vec (A : Type) : Nat -> Type\n  | nil : Vec A 0\n  | cons : forall {n : Nat}, A -> Vec A n -> Vec A (n + 1)\ninductive Fin : Nat -> Type\n  | zero : forall {n : Nat}, Fin (n + 1)\n  | succ : forall {n : Nat}, Fin n -> Fin (n + 1)\ndef List.length {A : Type} (xs : List A) : Nat :=\n  List.rec (fun (_ : List A) => Nat) 0 (fun (x : A) (t : List A) (r : Nat) => Nat.succ r) xs\ndef Vec.toList {A : Type} {n : Nat} (v : Vec A n) : List A :=\n  Vec.rec (fun (m : Nat) (_ : Vec A m) => List A) List.nil (fun (m : Nat) (a : A) (t : Vec A m) (r : List A) => List.cons a r) n v\ndef Fin.toNat {n : Nat} (i : Fin n) : Nat :=\n  Fin.rec (fun (m : Nat) (_ : Fin m) => Nat) (fun (m : Nat) => 0) (fun (m : Nat) (j : Fin m) (r : Nat) => Nat.succ r) n i\neval Vec.toList (Vec.cons 1 (Vec.cons 2 Vec.nil))\neval Fin.toNat (Fin.succ (Fin.succ Fin.zero) : Fin 3)\ntheorem toList_length {A : Type} {n : Nat} (v : Vec A n) : List.length (Vec.toList v) = n := by\n  induction v with m a t ih\n  rfl\n  exact Eq.congr Nat.succ ih' },
  { name: '索引合一:Fin 0 是空的', src: 'inductive Fin : Nat -> Type\n  | zero : forall {n : Nat}, Fin (n + 1)\n  | succ : forall {n : Nat}, Fin n -> Fin (n + 1)\ntheorem Fin.zero_elim {C : Prop} (i : Fin 0) : C := by\n  cases i' },
  { name: '索引合一:非空 Vec 的 cases', src: 'inductive Vec (A : Type) : Nat -> Type\n  | nil : Vec A 0\n  | cons : forall {n : Nat}, A -> Vec A n -> Vec A (n + 1)\ndef Vec.toList {A : Type} {n : Nat} (v : Vec A n) : List A :=\n  Vec.rec (fun (m : Nat) (_ : Vec A m) => List A) List.nil (fun (m : Nat) (a : A) (t : Vec A m) (r : List A) => List.cons a r) n v\ntheorem toList_ne_nil {A : Type} {n : Nat} (v : Vec A (n + 1)) (h : Vec.toList v = List.nil) : False := by\n  cases v with m a t\n  discriminate h' },
  { name: 'subst / injection', src: 'theorem succ_inj {m n : Nat} (h : Nat.succ m = Nat.succ n) : m = n := by\n  injection h\n  exact h_1\ntheorem subst_demo {A : Type} {a b : A} (h : a = b) (P : A -> Prop) (pa : P a) : P b := by\n  subst h\n  exact pa' },
  { name: '用策略寫資料定義:Vec.head / map', src: 'inductive Vec (A : Type) : Nat -> Type\n  | nil : Vec A 0\n  | cons : forall {n : Nat}, A -> Vec A n -> Vec A (n + 1)\ndef Vec.toList {A : Type} {n : Nat} (v : Vec A n) : List A :=\n  Vec.rec (fun (m : Nat) (_ : Vec A m) => List A) List.nil (fun (m : Nat) (a : A) (t : Vec A m) (r : List A) => List.cons a r) n v\ndef Vec.head {A : Type} {n : Nat} (v : Vec A (n + 1)) : A := by\n  cases v with m a t\n  exact a\ndef Vec.tail {A : Type} {n : Nat} (v : Vec A (n + 1)) : Vec A n := by\n  cases v with m a t\n  exact t\ndef Vec.map {A B : Type} (f : A -> B) {n : Nat} (v : Vec A n) : Vec B n := by\n  induction v with m a t ih\n  exact Vec.nil\n  exact Vec.cons (f a) ih\ndef Vec.cast {A : Type} {m n : Nat} (h : m = n) (v : Vec A m) : Vec A n := by\n  subst h\n  exact v\neval Vec.head (Vec.cons 7 (Vec.cons 8 Vec.nil))\neval Vec.toList (Vec.tail (Vec.cons 7 (Vec.cons 8 Vec.nil)))\neval Vec.toList (Vec.map Nat.succ (Vec.cons 1 (Vec.cons 2 Vec.nil)))\neval Vec.toList (Vec.cast (Eq.refl : 2 = 2) (Vec.cons 1 (Vec.cons 2 Vec.nil)))\ncheck Eq.rec' },
  { name: 'match 模式匹配(含結構遞迴)', src: 'inductive Vec (A : Type) : Nat -> Type\n  | nil : Vec A 0\n  | cons : forall {n : Nat}, A -> Vec A n -> Vec A (n + 1)\ndef Vec.toList {A : Type} {n : Nat} (v : Vec A n) : List A :=\n  match v with\n  | Vec.nil => List.nil\n  | Vec.cons a t => List.cons a (Vec.toList t)\ndef Vec.head {A : Type} {n : Nat} (v : Vec A (n + 1)) : A :=\n  match v with\n  | Vec.cons a t => a\ndef Vec.map {A B : Type} (f : A -> B) {n : Nat} (v : Vec A n) : Vec B n :=\n  match v with\n  | Vec.nil => Vec.nil\n  | Vec.cons a t => Vec.cons (f a) (Vec.map f t)\ndef Nat.double (n : Nat) : Nat :=\n  match n with\n  | Nat.zero => 0\n  | Nat.succ k => Nat.succ (Nat.succ (Nat.double k))\ntheorem Nat.zero_add2 (n : Nat) : 0 + n = n :=\n  match n with\n  | Nat.zero => (Eq.refl : 0 + 0 = 0)\n  | Nat.succ k => Eq.congr Nat.succ (Nat.zero_add2 k)\neval Vec.head (Vec.map Nat.double (Vec.cons 3 (Vec.cons 4 Vec.nil)))\neval Vec.toList (Vec.map Nat.double (Vec.cons 3 (Vec.cons 4 Vec.nil)))' },
  { name: 'auto:直覺主義命題邏輯', src: 'theorem and_comm2 {A B : Prop} : And A B -> And B A := by auto\ntheorem curry {A B C : Prop} : (And A B -> C) -> A -> B -> C := by auto\ntheorem contrapos {A B : Prop} : (A -> B) -> Not B -> Not A := by auto\ntheorem dist {A B C : Prop} : And A (Or B C) -> Or (And A B) (And A C) := by auto\ntheorem chain {A B C D : Prop} : (A -> B) -> (B -> C) -> (C -> D) -> A -> D := by auto\ntheorem nn_em {A : Prop} : Not (Not (Or A (Not A))) := by auto' },
  { name: 'auto:一階、∃ 與等式', src: 'theorem socrates {Man Mortal : Nat -> Prop} {s : Nat} (h : forall (x : Nat), Man x -> Mortal x) (m : Man s) : Mortal s := by auto\ntheorem ex_swap2 {P Q : Nat -> Prop} : Exists (fun (x : Nat) => And (P x) (Q x)) -> Exists (fun (x : Nat) => And (Q x) (P x)) := by auto\ntheorem two_plus_two : 2 + 2 = 4 := by auto\ntheorem eq_flip {A : Type} {a b c : A} (h1 : a = b) (h2 : c = b) : a = c := by\n  rw h1\n  auto' },
  { name: 'tauto:古典邏輯(依賴 Classical.em)', src: 'theorem peirce {A B : Prop} : ((A -> B) -> A) -> A := by tauto\ntheorem em2 {A : Prop} : Or A (Not A) := by tauto\ntheorem dne {A : Prop} : Not (Not A) -> A := by tauto\ntheorem demorgan {A B : Prop} : Not (And A B) -> Or (Not A) (Not B) := by tauto\ntheorem uses_peirce {A B : Prop} : ((A -> B) -> A) -> A := peirce' },
  { name: 'auto 做不到的(錯誤示範)', src: 'theorem peirce2 {A B : Prop} : ((A -> B) -> A) -> A := by auto\ntheorem or_any {A B : Prop} : Or A B := by tauto' },
  { name: '自己宣告歸納型別', src: 'inductive Tree (A : Type) : Type\n  | leaf : Tree A\n  | node : Tree A -> A -> Tree A -> Tree A\ndef Tree.size {A : Type} (t : Tree A) : Nat :=\n  Tree.rec (fun (_ : Tree A) => Nat) 0 (fun (l : Tree A) (x : A) (r : Tree A) (ihl : Nat) (ihr : Nat) => Nat.succ (ihl + ihr)) t\neval Tree.size (Tree.node (Tree.node Tree.leaf 1 Tree.leaf) 2 Tree.leaf)\ncheck Tree.ind' },
  { name: '項模式的證明', src: 'theorem and_left {A B : Prop} (h : And A B) : A := And.ind (fun (_ : And A B) => A) (fun (a : A) (b : B) => a) h' },
  { name: '非嚴格正向的型別(錯誤示範)', src: 'inductive Bad : Type\n  | mk : (Bad -> Nat) -> Bad' },
  { name: '型別錯誤(錯誤示範)', src: 'check Nat.succ List.nil\ntheorem wrong (n : Nat) : n = 0 := by\n  rfl' },
];
const API = { runScript, report, examples, MuError, kernel: { infer, A, C, S, whnf, show } };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else globalThis.Mu = API;
})();
