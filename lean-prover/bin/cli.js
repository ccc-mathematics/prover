#!/usr/bin/env node
// 用法: node bin/cli.js --demo | 檔案.lean [--trace] | (標準輸入)
const fs = require('fs'), L = require('../src/lean.js');
const a = process.argv.slice(2), trace = a.includes('--trace'), files = a.filter(x => !x.startsWith('--'));
let text;
if (a.includes('--demo') || (!files.length && process.stdin.isTTY)) text = L.examples.map(e => e.src).join('\n\n');
else text = fs.readFileSync(files[0] || 0, 'utf8');
let bad = 0;
for (const t of L.splitThms(text)) {
  try { const r = L.runThm(t); console.log(L.report(r, trace) + '\n'); if (r.status !== 'done') bad++; }
  catch (e) { console.log('錯誤:' + e.message + '\n'); bad++; }
}
process.exit(bad ? 1 : 0);
