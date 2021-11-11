// Runner for (compiled) Waml programs
//
// Synopsis:
//   node --experimental-wasm-gc js/waml.js waml-module ...
//
// Requires node 16 or newer.

'use strict';

let fs = require('fs');

let registry = {__proto__: null};

async function link(name) {
  if (! (name in registry)) {
    let binary = fs.readFileSync(name + ".wasm");
    let module = await WebAssembly.compile(new Uint8Array(binary));
    for (let im of WebAssembly.Module.imports(module)) {
      await link(im.module);
    }
    let instance = await WebAssembly.instantiate(module, registry);
    registry[name] = instance.exports;
  }
  return registry[name];
}

async function run(name) {
  let exports = await link(name);
  return exports.return;
}

process.argv.splice(0, 2);
for (let file of process.argv) {
  run(file);
}
