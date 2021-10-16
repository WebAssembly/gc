// Runner for (compiled) Wob programs
//
// Synopsis:
//   node --experimental-wasm-gc js/wob.js wob-module ...
//
// Requires node 16 or newer.

'use strict';

let fs = require('fs');

function arraybuffer(bytes) {
  let buffer = new ArrayBuffer(bytes.length);
  let view = new Uint8Array(buffer);
  for (let i = 0; i < bytes.length; ++i) {
    view[i] = bytes.charCodeAt(i);
  }
  return buffer;
}

let registry = {__proto__: null};

async function link(name) {
  if (! (name in registry)) {
    let bytes = fs.readFileSync(name + ".wasm", "binary");
    let binary = arraybuffer(bytes);
    let module = await WebAssembly.compile(binary);
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
