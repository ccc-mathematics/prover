#!/usr/bin/env node
// 用法: node bin/cli.js --demo | 檔案.mu [--trace] | (標準輸入)
const fs = require('fs'), M = require('../src/mu.js');
const a = process.argv.slice(2), trace = a.includes('--trace'), files = a.filter(x => !x.startsWith('--'));
if (a.includes('--demo') || (!files.length && process.stdin.isTTY)) {
  for (const e of M.examples) console.log('-- ' + e.name + '\n' + M.report(M.runScript(e.src), trace) + '\n');
} else {
  const r = M.runScript(fs.readFileSync(files[0] || 0, 'utf8')); console.log(M.report(r, trace)); process.exit(r.ok ? 0 : 1);
}
