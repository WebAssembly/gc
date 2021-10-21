# Wln -- Simple Wasm linker

A lightweight, language-agnostic static linker for merging Wasm modules.

## Overview

Wln is a simple linker for Wasm. It takes a list of Wasm binaries (or text files) and merges them into a single Wasm binary (or text file).

The linker does not make any specific assumptions about the form of the input modules, it simply matches up imports and exports.

For example, this invocation links the binaries `a.wasm`, `b.wasm`, and t`c.wasm` and produces one combined `o.wasm`:
```
wln a.wasm b.wasm c.wasm -o o.wasm
```


## Usage

### Building

Saying
```
make
```
in the `wln` directory should produce a binary `wln` in that directory.


### Invocation

The linker can freely consume and produce both binary and textual Wasm modules. For example:

* `wln a.wasm b.wasm -o c.wasm` operates in binary mode.
* `wln a.wat b.wat -o c.wat` operates in textual mode.
* `wln a.wat b.wasm -o c.wasm` mixes both binary and textual mode.
* `wln a.wasm -o a.wat` converts binary to textual representation.
* `wln a.wat -o a.wasm` converts textual to binary representation.
* `wln -o e.wasm` produces an empty binary module.

See `wob -h` for further options.


### Semantics

Let the *output file* be the file name provided with the `-o` option. Let the *input files* be the other file names given on the command line. Then:

* Each input file is interpreted as an *input module name* by removing its file extension. (There is not currently any relative path resolution.)

* Each module name in an import is looked up among the input module names.

* Each item name in an import is looked up among the export names of the respective module.

* If an import module name is among the input modules, but does not export the respective item, or the item has the wrong type, then an error is raised.

* The imports of the output module are all accumulated imports whose module name is not among the input modules.

* The exports of the output module are the exports of the last input module.

* If more than one input module has a start function, then a new sart function is synthesized for the output module, which calls all input start functions in order.

* Input files have to be provided in order, that is, an import can only match against prior module names.

* If no input files are given, an empty module is produced.

There is no attempt to dedupe any definitions.

Currently, it is an error if more than one of the linked modules defines a ememory (this will be allowed once the [multi-memory proposal](https://github.com/WebAssembly/multi-memory/) has been included in Wasm).


### Example

Consider the following modules:

* module `a.wat`:
  ```
  (module
    (func $0 (export "f") (nop))
    (func $1 (block))
    (func $2 (export "g") (call 1))
    (start 0)
  )
  ```

* module `d/b.wat`:
  ```
  (module
    (func $0 (import "a" "f"))
    (func $1 (import "e" "a"))
    (func $2 (export "f") (call 0))
    (func $3 (export "h") (call 1) (call 2))
  )
  ```

* module `c.wat`:
  ```
  (module
    (func $0 (import "a" "g"))
    (func $1 (import "d/b" "h"))
    (func $2 (import "e" "f"))
    (func $3 (export "k") (call 0) (call 1) (call 2))
    (start 2)
  )
  ```

Then the invocation:
```
wln a.wat d/b.wat c.wat -o o.wat
```
will produce the equivalent of the following:

* module `o.wat`:
  ```
  (module
    ;; leftover imports from "d/b"
    (func $0 (import "e" "a"))

    ;; leftover imports from "c"
    (func $1 (import "e" "f"))

    ;; items from "a"
    (func $2 (nop))              ;; "f"
    (func $3 (block))
    (func $4 (call 3))           ;; "g"

    ;; items from "d/b"
    (func $5 (call 2))           ;; "f"
    (func $6 (call 0) (call 5))  ;; "h"

    ;; items from "c"
    (func $7 (export "k") (call 4) (call 6) (call 1))

    ;; synthesized start function
    (func $8 (call 2) (call 1))
    (start 8)
  )
  ```
