#!/usr/bin/env node
// 用法: node bin/cli.js --demo | 檔案.lc [--trace] | (標準輸入)
const fs = require('fs'), C = require('../src/cube.js');
const a = process.argv.slice(2), trace = a.includes('--trace'), files = a.filter(x => !x.startsWith('--'));
const srcs = a.includes('--demo') || (!files.length && process.stdin.isTTY) ? C.examples.map(e => '-- ' + e.name + '\n' + e.src) : [fs.readFileSync(files[0] || 0, 'utf8')];
let bad = 0;
for (const s of srcs) { const r = C.runScript(s); console.log(C.report(r, trace) + '\n'); if (!r.ok) bad++; }
process.exit(a.includes('--demo') ? 0 : bad ? 1 : 0);
