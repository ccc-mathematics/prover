"use strict";

const Univ = level => ({ t: "Univ", level });
const Var = name => ({ t: "Var", name });
const Lam = (x, type, body) => ({ t: "Lam", x, type, body });
const Pi = (x, type, body) => ({ t: "Pi", x, type, body });
const App = (fn, arg) => ({ t: "App", fn, arg });
const Hole = id => ({ t: "Hole", id });

function fv(term, bound = new Set()) {
  switch (term.t) {
    case "Var": return bound.has(term.name) ? new Set() : new Set([term.name]);
    case "Univ": case "Hole": return new Set();
    case "App": {
      const s = fv(term.fn, bound);
      for (const v of fv(term.arg, bound)) s.add(v);
      return s;
    }
    case "Lam": case "Pi": {
      const s = fv(term.type, bound);
      const b2 = new Set(bound); b2.add(term.x);
      for (const v of fv(term.body, b2)) s.add(v);
      return s;
    }
  }
}

function freshName(base, forbidden) {
  let name = base || "x";
  while (forbidden.has(name)) name += "'";
  return name;
}

function subst(term, x, replacement) {
  switch (term.t) {
    case "Var": return term.name === x ? replacement : term;
    case "Univ": case "Hole": return term;
    case "App": return App(subst(term.fn, x, replacement), subst(term.arg, x, replacement));
    case "Lam": case "Pi": {
      const newType = subst(term.type, x, replacement);
      if (term.x === x) return { ...term, type: newType };
      const fvRepl = fv(replacement);
      let v = term.x;
      let body = term.body;
      if (fvRepl.has(v)) {
        const forbidden = new Set([...fvRepl, ...fv(body), x]);
        const z = freshName(v, forbidden);
        body = subst(body, v, Var(z));
        v = z;
      }
      const newBody = subst(body, x, replacement);
      return term.t === "Lam" ? Lam(v, newType, newBody) : Pi(v, newType, newBody);
    }
  }
}

function normalize(term, env = {}) {
  switch (term.t) {
    case "Var":
      return env[term.name] ? normalize(env[term.name], env) : term;
    case "Univ": case "Hole": return term;
    case "App": {
      const fn = normalize(term.fn, env);
      const arg = normalize(term.arg, env);
      if (fn.t === "Lam") return normalize(subst(fn.body, fn.x, arg), env);
      return App(fn, arg);
    }
    case "Lam":
      return Lam(term.x, normalize(term.type, env), normalize(term.body, env));
    case "Pi":
      return Pi(term.x, normalize(term.type, env), normalize(term.body, env));
  }
}

function alphaEq(t1, t2) {
  const n1 = normalize(t1);
  const n2 = normalize(t2);
  if (n1.t !== n2.t) return false;
  switch (n1.t) {
    case "Univ": return n1.level === n2.level;
    case "Var": return n1.name === n2.name;
    case "Hole": return n1.id === n2.id;
    case "App": return alphaEq(n1.fn, n2.fn) && alphaEq(n1.arg, n2.arg);
    case "Lam": case "Pi": {
      if (!alphaEq(n1.type, n2.type)) return false;
      if (n1.x === n2.x) return alphaEq(n1.body, n2.body);
      const z = freshName("z", new Set([...fv(n1.body), ...fv(n2.body)]));
      const b1 = subst(n1.body, n1.x, Var(z));
      const b2 = subst(n2.body, n2.x, Var(z));
      return alphaEq(b1, b2);
    }
  }
}

function pretty(term, prec = 0) {
  const par = (s, c) => c ? "(" + s + ")" : s;
  switch (term.t) {
    case "Univ": return term.level === 0 ? "Prop" : "Type" + (term.level > 1 ? term.level : "");
    case "Var": return term.name;
    case "Hole": return "?" + term.id;
    case "App": {
      const chain = [];
      let cur = term;
      while (cur.t === "App") { chain.unshift(cur.arg); cur = cur.fn; }
      const s = [pretty(cur, 2), ...chain.map(a => pretty(a, 3))].join(" ");
      return par(s, prec > 2);
    }
    case "Lam":
      return par("λ " + term.x + " : " + pretty(term.type, 0) + ", " + pretty(term.body, 0), prec > 0);
    case "Pi": {
      if (!fv(term.body).has(term.x)) {
        return par(pretty(term.type, 2) + " -> " + pretty(term.body, 1), prec > 1);
      }
      return par("Π " + term.x + " : " + pretty(term.type, 0) + ", " + pretty(term.body, 0), prec > 0);
    }
  }
}

function infer(term, ctx = {}) {
  switch (term.t) {
    case "Univ":
      return Univ(term.level + 1);
    case "Var": {
      if (!ctx[term.name]) throw new Error("未綁定的變數: " + term.name);
      return ctx[term.name];
    }
    case "Hole":
      throw new Error("證明中仍有未解決的目標洞: ?" + term.id);
    case "Pi": {
      const tyT = infer(term.type, ctx);
      const normT = normalize(tyT);
      if (normT.t !== "Univ") throw new Error("領域型別必須是宇宙(Type/Prop)");
      const extended = { ...ctx, [term.x]: term.type };
      const tyB = infer(term.body, extended);
      const normB = normalize(tyB);
      if (normB.t !== "Univ") throw new Error("目標型別必須是宇宙(Type/Prop)");
      return normB.level === 0 ? Univ(0) : Univ(Math.max(normT.level, normB.level));
    }
    case "Lam": {
      infer(term.type, ctx);
      const extended = { ...ctx, [term.x]: term.type };
      const bodyTy = infer(term.body, extended);
      return Pi(term.x, term.type, bodyTy);
    }
    case "App": {
      const fnTy = normalize(infer(term.fn, ctx));
      if (fnTy.t !== "Pi") throw new Error("嘗試呼叫非函數物件: " + pretty(term.fn));
      const argTy = infer(term.arg, ctx);
      if (!alphaEq(fnTy.type, argTy)) {
        throw new Error(
          "參數型別不符! 預期: " + pretty(fnTy.type) + " 但得到: " + pretty(argTy) + " 在套用 " + pretty(term.fn) + " 於 " + pretty(term.arg) + " 時"
        );
      }
      return normalize(subst(fnTy.body, fnTy.x, term.arg));
    }
  }
}

module.exports = {
  Univ, Var, Lam, Pi, App, Hole,
  subst, normalize, alphaEq, infer, pretty, freshName, fv
};
