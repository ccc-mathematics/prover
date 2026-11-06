const L = require('../src/lean.js'); let fail = 0;
const ok = (c, m) => { console.log((c ? 'PASS  ' : 'FAIL  ') + m); if (!c) fail++; };
for (const e of L.examples) ok(L.runThm(e.src).status === 'done', e.name);
ok(L.runThm('theorem t : P -> Q := by\n  intro h\n  exact h').status === 'error', '錯誤的策略會被拒絕');
ok(L.runThm('theorem t : P -> P := by\n  intro h').status === 'open', '未完成的證明回報 open');
ok(L.runThm('theorem t : P := by\n  sorry').status === 'sorry', 'sorry 會被標記');
try { L.check({ r: 'andE1', p: { r: 'hyp', n: 'h' } }, [['h', { t: 'atom', n: 'P', a: [] }]]); ok(false, '核心應拒絕偽造的證明項'); }
catch (e) { ok(true, '核心拒絕偽造的證明項'); }
process.exit(fail ? 1 : 0);
