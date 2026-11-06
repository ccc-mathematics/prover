#!/usr/bin/env node
"use strict";
const fs = require("fs");
const readline = require("readline");
const { parse } = require("./parser");
const { infer, pretty } = require("./core");
const { ProofState } = require("./prover");

const args = process.argv.slice(2);

function runScript(content) {
  const lines = content.split("\n");
  let i = 0;
  while (i < lines.length) {
    const line = lines[i].trim();
    if (!line || line.startsWith("--")) { i++; continue; }
    if (line.startsWith("theorem") || line.startsWith("lemma")) {
      const headerMatch = line.match(/^(?:theorem|lemma)\s+([A-Za-z_][\w']*)\s*:\s*(.+?)\s*:=\s*by$/);
      if (!headerMatch) throw new Error("無法解析定理標頭: " + line);
      const name = headerMatch[1];
      const goalTerm = parse(headerMatch[2]);
      const st = new ProofState(goalTerm);
      console.log("\x1b[36m=== 證明定理: " + name + " ===\x1b[0m");
      console.log("目標: " + pretty(goalTerm) + "\n");
      i++;
      while (i < lines.length) {
        const tLine = lines[i].trim();
        if (tLine === "qed" || tLine === "end") { i++; break; }
        if (tLine && !tLine.startsWith("--")) {
          console.log("  > " + tLine);
          st.runTactic(tLine);
          if (st.goals.length > 0) {
            console.log("    \x1b[90m剩餘目標: " + st.goals.length + " 個 | 當前: ⊢ " + pretty(st.goals[0].target) + "\x1b[0m");
          }
        }
        i++;
      }
      const pf = st.verify();
      console.log("\x1b[32m✔ 證明完成! 核心檢查通過.\x1b[0m");
      console.log("證明項 (Lambda Term):\n  " + pretty(pf) + "\n");
    } else {
      i++;
    }
  }
}

if (args.length > 0) {
  const file = args[0];
  const src = fs.readFileSync(file, "utf8");
  try {
    runScript(src);
  } catch (e) {
    console.error("\x1b[31m錯誤: " + e.message + "\x1b[0m");
    process.exit(1);
  }
} else {
  console.log("\x1b[35m=== Lambda-Cube 互動式 REPL 證明器 ===\x1b[0m");
  console.log("輸入範例: theorem id : Pi A:Prop, A -> A := by");
  const rl = readline.createInterface({ input: process.stdin, output: process.stdout });
  let buffer = [];
  rl.setPrompt("CoC> ");
  rl.prompt();

  rl.on("line", line => {
    buffer.push(line);
    if (line.trim() === "qed" || line.trim().startsWith("end")) {
      try {
        runScript(buffer.join("\n"));
      } catch (err) {
        console.log("\x1b[31m" + err.message + "\x1b[0m");
      }
      buffer = [];
    }
    rl.prompt();
  });
}
