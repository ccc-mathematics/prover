#!/usr/bin/env node
// 用法: node bin/cli.js --demo | 檔案.mu [--trace] [--cert] | (標準輸入)
//   --cert:印出每個定理被核心檢查過的證明項(certificate)
const fs = require('fs'), M = require('../src/mu.js');
const a = process.argv.slice(2), trace = a.includes('--trace'), cert = a.includes('--cert'), files = a.filter(x => !x.startsWith('--'));
if (a.includes('--demo') || (!files.length && process.stdin.isTTY)) {
  for (const e of M.examples) console.log('-- ' + e.name + '\n' + M.report(M.runScript(e.src), trace, cert) + '\n');
} else {
  const r = M.runScript(fs.readFileSync(files[0] || 0, 'utf8')); console.log(M.report(r, trace, cert)); process.exit(r.ok ? 0 : 1);
}
