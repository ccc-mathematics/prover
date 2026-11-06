"use strict";
const { Univ, Var, Lam, Pi, App } = require("./core");

const GREEK = { "λ": "\\\\", "\\": "\\\\", "Π": "Pi ", "forall": "Pi ", "∀": "Pi ", "->": "->", "→": "->" };

function lex(str) {
  const s = str.replace(/[λ\\Π∀→]/g, c => GREEK[c] || c);
  const regex = /->|:=|:|Prop|Type\d*|Pi|\\|\(|\)|,|\.|[A-Za-z_][\w']*/g;
  return s.match(regex) || [];
}

function parse(src) {
  const tokens = lex(src);
  let p = 0;
  const peek = () => tokens[p];
  const next = () => tokens[p++];
  const expect = t => {
    const got = next();
    if (got !== t) throw new Error("語法錯誤: 預期 \"" + t + "\" 但得到 \"" + (got || "EOF") + "\"");
  };

  function parseExpr() { return parseArrow(); }

  function parseArrow() {
    let l = parsePi();
    if (peek() === "->") {
      next();
      const r = parseArrow();
      return Pi("_anon" + Math.random().toString(36).substr(2, 4), l, r);
    }
    return l;
  }

  function parsePi() {
    if (peek() === "Pi") {
      next();
      const v = next();
      expect(":");
      const ty = parseExpr();
      expect(",");
      const body = parseExpr();
      return Pi(v, ty, body);
    }
    if (peek() === "\\\\") {
      next();
      const v = next();
      expect(":");
      const ty = parseExpr();
      expect(",");
      const body = parseExpr();
      return Lam(v, ty, body);
    }
    return parseApp();
  }

  function parseApp() {
    let fn = parseAtom();
    while (p < tokens.length && !["->", ")", ",", ":", ":="].includes(peek())) {
      const arg = parseAtom();
      fn = App(fn, arg);
    }
    return fn;
  }

  function parseAtom() {
    const t = next();
    if (!t) throw new Error("語法錯誤: 不預期的結尾");
    if (t === "Prop") return Univ(0);
    if (t === "Type") return Univ(1);
    if (t.startsWith("Type")) return Univ(parseInt(t.slice(4)) || 1);
    if (t === "(") {
      const e = parseExpr();
      expect(")");
      return e;
    }
    if (/^[A-Za-z_][\w']*$/.test(t)) return Var(t);
    throw new Error("無法解析的標記: " + t);
  }

  const res = parseExpr();
  if (p < tokens.length) throw new Error("有多餘符號: " + tokens.slice(p).join(" "));
  return res;
}

module.exports = { parse, lex };
