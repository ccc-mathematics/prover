const fs = require('fs'), path = require('path'), root = path.join(__dirname, '..');
fs.writeFileSync(path.join(root, 'web/index.html'), fs.readFileSync(path.join(root, 'web/template.html'), 'utf8')
  .split('/*LEAN*/').join(fs.readFileSync(path.join(root, 'src/lean.js'), 'utf8')));
console.log('已產生 web/index.html');
