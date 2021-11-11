# Wob -- Wasm Objects

An experimental object-oriented language and implementation for exploring and evaluating the Wasm [GC proposal](https://github.com/WebAssembly/gc/#gc-proposal-for-webassembly).

## Overview

Wob is a typed mini-OO language in the style of C# and friends. It is meant to be representative of the most relevant problems that arise when compiling such languages to Wasm with GC extensions. These arguably are:

* generics
* classes
* safe downcasts
* separate compilation

To that end, Wob features:

* primitive data types
* tuples and arrays
* functions and closures
* classes and inheritance
* first-class generics
* safe runtime casts
* simple modules with separate compilation and client-side linking

For simplicity, Wob omits various other common features, such as access control to classes and modules, more advanced control constructs, or sophisticated type inference, which are mostly independent from code generation and data representation problems. It also doesn't currently have interface types.

The `wob` implementation encompasses:

* Interpreter
* Compiler to Wasm (WIP)
* A read-eval-print-loop that can run either interpreted or compiled code

The language is fully implemented in the interpreter, but the compiler does not yet support closures. It does, however, fully implement garbage-collected objects, tuples, arrays, text strings, classes, casts, and generics, making use of [most of the constructs](#under-the-hood) in the GC proposal's MVP.

For example, here is a short transcript of a REPL session with [`wob -c -x`](#invocation):
```
proposals/gc/wob$ ./wob -x -c
wob 0.1 interpreter
> func f(x : Int) : Int { x + 7 }; f(5);
(module
  (type $0 (func))
  (type $1 (func (param i32) (result i32)))
  (global $0 (mut i32) (i32.const 0))
  (func $0 (type 0) (i32.const 5) (call 1) (global.set 0))
  (func $1 (type 1) (local.get 0) (i32.const 7) (i32.add))
  (export "return" (global 0))
  (export "f" (func 1))
  (start 0)
)
12 : Int
f : Int -> Int
> 
```
See [below](#under-the-hood) for a brief explanation regarding the produced code.


## Usage

### Building

Saying
```
make
```
in the `wob` directory should produce a binary `wob` in that directory.

### Invocation

The `wob` binary is both compiler and REPL. For example:

* `wob` starts the interactive prompt, using the interpreter.
* `wob -c` starts the interactive prompt, but each input is compiled and run via Wasm.
* `wob -c -x` same, but the generated Wasm code is also shown for each input.
* `wob -r <file.wob>` batch-executes the file via the interpreter.
* `wob -r -c <file.wob>` batch-executes the file via Wasm.
* `wob -c <file.wob>` compiles the file to `<file.wasm>`.

See `wob -h` for further options.

Points of note:

* The Wasm code produced is self-contained with no imports except the small Wob runtime system (unless the source declares explicit imports of other Wob modules). Consequently, it can run in any Wasm environment supporting the GC proposal.

* The compiler even supports a *headless* mode in which the relevant parts of the runtime system is included into each module.

* That means that there is no I/O. However, a program can communicate results via module exports or run assertions.

* When batch-executing, all Wasm code is itself executed via the Wasm reference interpreter, so don't expect performance miracles.

### Test Suite

Run
```
make test
```
to run the interpreter against the tests, or
```
make wasmtest
```
to run the compiler.


## Syntax

### Types

```
typ ::=
  id ('<' typ,* '>')?                      named use
  '(' typ,* ')'                            tuple
  typ '[' ']'                              array
  typ [' ']' '!'                           readonly array
  typ '$'                                  boxed
  ('<' id,* '>')? '(' typ,* ')' '->' typ   function
  typ '->' typ                             function (shorthand)
```

Notes:

* Generics can only be instantiated with _boxed_ types, which excludes the primitive data types `Bool`, `Byte`, `Int`, and `Float`. These can be converted to boxed types via `Bool$`, `Int$`, etc. There is no autoboxing.

* Readonly arrays are a supertype of regular arrays, and only they allow covariant subtyping on the element type.


### Expressions

```
unop  ::= '+' | '-' | '^' | '!'
binop ::= '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '<<' | '>>'
relop ::= '==' | '!=' | '<' | '>' | '<=' | '>='
logop ::= '&&' | '||'

exp ::=
  int                                      integer literal
  float                                    floating-point literal
  text                                     text string
  id                                       variable use
  unop exp                                 unary operator
  exp binop exp                            binary operator
  exp relop exp                            comparison operator
  exp logop exp                            logical operator
  exp ':=' exp                             assignment
  '(' exp,* ')'                            tuple
  '[' exp,* ']'                            array
  exp '.' nat                              tuple access
  exp '.' id                               object access
  exp '[' exp ']'                          array or text access
  '#' exp                                  array or text length
  exp ('<' typ,* '>')? '(' exp,* ')'       function call
  'new' id ('<' typ,* '>')? '(' exp,* ')'  class instantiation
  'new' typ '[' exp ']' '(' exp ')'        array instantiation
  exp '$'                                  box value
  exp '.' '$'                              unbox boxed value
  exp ':' typ                              static type annotation
  exp ':>' typ                             dynamic type cast
  'assert' exp                             assertion
  'return' exp?                            function return
  block                                    block
  'if' exp block ('else' block)?           conditional
  'while' exp block                        loop
  'func' ('<' id,* '>')? '(' param,* ')'   anonymous function (shorthand)
      (':' typ) block

block :
  '{' dec;* '}'                            block
```
Notes:

* There is no distinction between expressions and statements: a block can be used in any expression context and it evaluates to the value of its last expression, or `()` (the empty tuple) if its last `dec` isn't an expression.

* In the REPL, the entire input is treated as a block, and its result is the input result.

* An `assert` failure is indicated by executing an `unreachable` instruction in Wasm and thereby trapping.


### Declarations
```
param ::=
  id ':' typ

dec ::=
  exp                                             expression
  'let' id (':' typ)? '=' exp                     immutable binding
  'var' id ':' typ '=' exp                        mutable binding
  'func' id ('<' id,* '>')? '(' param,* ')'       function
      (':' typ) block
  'class' id ('<' id,* '>')? '(' param,* ')'      class
      ('<:' id ('<' typ,* '>')? '(' exp,* ')')?
      block
  'type' id ('<' id,* '>')? '=' typ               type alias
```

Note:

* All scoping is strictly linear, i.e., it is not currently possible to forward-reference a binding, not even inside a class, except through the use of `this`. Functions and classes can, however, recursively refer to themselves.

* Classes have just one constructor, whose parameters are the class definition's parameters and whose body is the class body.

* Inside class scope, immutable `let` bindings can only refer to the class parameters or `let` variables from a super-class, or any bindings from outer scope; they have neither access to methods nor `this`. That prevents the ability to observe uninitialised `let` through dispatch, which is crucial, since these have to be represented as immutable Wasm fields on the instance.

* Classes are nominal types.

* For simplicity, there is no access control for objects.


### Modules
```
imp ::=
  'import' id? '{' id,* '}' 'from' text           import

module ::=
  imp;* dec;*
```

Notes:

* A module executes by executing all contained declarations in order.

* For simplicity, there is no access control beyond using blocks, that is, all top-level declarations are exported.

* Imports are loaded eagerly and recursively. When an import specifies a qualifying identifier `M`, then all names from the import list are renamed to include the prefix `M` -- this is a hack to avoid the introduction of name spacing constructs.

* With batch compilation, modifying a module generally requires recompiling its dependencies, otherwise Wasm linking may fail.


### Prebound Identifiers

#### Types
```
Bool  Byte  Int  Float  Text  Object
```

#### Values
```
true  false  null  nan  this
```

Notes:

* The `this` identifier is only bound within a class.


## Examples

### Functions
```
func fac(x : Int) : Int {
  if x == 0 { return 1 };
  x * fac(x - 1);
};

assert fac(5) == 120;
```
```
func foreach(a : Int[], f : Int -> ()) {
  var i : Int = 0;
  while i < #a {
    f(a[i]);
    i := i + 1;
  }
};

let a = [1, 2, 5, 6, -8];
var sum : Int = 0;
foreach(a, func(k : Int) { sum := sum + k });
assert sum == 6;
```

### Generics
```
func fold<T, R>(a : T[], x : R, f : (Int, T, R) -> R) : R {
  var i : Int = 0;
  var r : R = x;
  while (i < #a) {
    r := f(i, a[i], r);
    i := i + 1;
  };
  return r;
};
```
```
func f<X>(x : X, f : <Y>(Y) -> Y) : (Int, X, Float) {
  let t = (1, x, 1e100);
  (f<Int$>(t.0$), f<X>(t.1), f<Float$>(t.2$));
};

let t = f<Bool$>(false$, func<T>(x : T) : T { x });
assert t.0 == 1;
assert !t.1;
assert t.2 == 1e100;
```

### Classes
```
class Counter(x : Int) {
  var c : Int = x;
  func get() : Int { return c };
  func set(x : Int) { c := x };
  func inc() { c := c + 1 };
};

class DCounter(x : Int) <: Counter(x) {
  func dec() { c := c - 1 };
};

class ECounter(x : Int) <: DCounter(x*2) {
  func inc() { c := c + 2 };
  func dec() { c := c - 2 };
};

let e = new ECounter(8);
```

### Modules
```
// Module "intpair"
type IntPair = (Int, Int);

func pair(x : Int, y : Int) : IntPair { (x, y) };
func fst(p : IntPair) : Int { p.0 };
func snd(p : IntPair) : Int { p.1 };
```
A client:
```
import IP_{pair, fst} from "intpair";

let p = IP_pair(4, 5);
assert IP_fst(p) == 4;
```

## Under the Hood


### Use of GC instructions

The compiler makes use of the following constructs from the GC proposal.

#### Types
```
i8
anyref  eqref  dataref  i31ref  (ref $t)  (ref null $t)  (rtt n $t)
struct  array
```
(Currently unused is `i16`).

#### Instructions
```
ref.eq
ref.is_null  ref.as_non_null  ref.as_i31  ref.as_data  ref.cast
i31.new  i31.get_u
struct.new  struct.get  struct.get_u  struct.set
array.new  array.new_default  array.get  array.get_u  array.set  array.len
rtt.canon  rtt.sub
```

(Currently unused are the remaining `ref.is_*` and `ref.as_*` instructions, `ref.test`, the `br_on_*` instructions, the signed `*.get_s` instructions, and `struct.new_default`.)


### Value representations

Wob types are lowered to Wasm as shown in the following table.

| Wob type | Wasm value type | Wasm field type |
| -------- | --------------- | --------------- |
| Bool     | i32             | i8              |
| Byte     | i32             | i8              |
| Int      | i32             | i32             |
| Float    | f64             | f64             |
| Bool$    | i31ref          | eqref           |
| Byte$    | i31ref          | eqref           |
| Int$     | ref (struct i32)| eqref           |
| Float$   | ref (struct f64)| eqref           |
| Text     | ref (array i8)  | eqref           |
| Object   | ref (struct)    | eqref           |
| (Float,Text)|ref (struct f64 eqref)| eqref   |
| Float[]  | ref (array f64) | eqref           |
| Text[]   | ref (array eqref)| eqref          |
| C        | ref (struct (ref $vt) ...)| eqref |
| <T>      | eqref           | eqref           |

Notably, all fields of boxed type have to be represented as `eqref`, in order to be compatible with [generics](#generics).

Types and type parameters have a [runtime representation](#runtime-type-represetation) as well, in order to enable casts over generic types.


### Bindings

Wob bindings are compiled to Wasm as follows.

| Wob declaration | in global scope | in func/block scope | in class scope |
| --------------- | --------------- | ------------------- | -------------- |
| `let`           | mutable `global`| `local`          | immutable field in instance struct |
| `var`           | mutable `global`| `local`             | mutable field in instance struct |
| `func`          | `func`          | not supported yet   | immutable field in dispatch struct |
| `class`         | immutable `global`| not supported yet | not supported yet |

Note that all global declarations have to be compiled into mutable globals, since they could not be initialised otherwise.

### Object representation

Objects are represented in the obvious manner, as a struct whose first field is a reference to the dispatch table, while the rest of the fields represent:

* class type arguments (immutable)
* constructor arguments (immutable)
* `let` fields (immutable)
* `var` fields (mutable)

of the class and its super classes, in definition order. All fields but `var` ones are immutable. Type arguments are represented as [runtime type](#runtime-type-representation), and used to check casts. Identical (type or value) arguments just passed forward to a super class are not currently deduped, but could be.

The dispatch table contains references to the function of the class and its super classes, in definition order. In addition, the last field of each dispatch table is a pointer to itself. This is also duplicated in place by dispatch tables for subclasses, so that each dispatch table is interleaved with references to the dispatch tables of all its super classes. The type of these references is `eqref`, and it is used to implement the class check for explicit casts. That is, the identity of dispatch tables is used as a proxy for class identities.

For example, the dispatch tables for the classes in the following snippet,
```
class C() {
  func f() {};
};
class D() <: C() {
  func g() {};
  func h() {};
};
class E() <: D() {
  func f() {};  // override
};
```
are:
```
$disp_C = [ $f_C | $disp_C ]
$disp_D = [ $f_C | $disp_C | $g_D | $h_D | $disp_D ]
$disp_E = [ $f_E | $disp_C | $g_D | $h_D | $disp_D | $disp_E ]
```
To check that an object's class is a subclass of `D`, the code first uses `br_on_cast` to down cast the object to the expected representation, which also implies that its dispatch table contains a slot for `$disp_D`. It then checks that the reference in that slot is equal to class `D`'s dispatch table. Finally, it checks that the [runtime types](#runtime-type-representation) for generic parameters match up.


### Class representation

Class declarations translate to a global binding a class _descriptor_, which is represented as a struct with the following fields:

| Index | Type | Description |
| ----- | ---- | ----------- |
| 0     | ref (struct ...) | Dispatch table |
| 1     | rtt $C | Instance RTT |
| 2     | ref (func ...) | Constructor function |
| 3     | ref (func ...) | Pre-allocation |
| 4     | ref (func ...) | Post-allocation |
| 5     | ref $Super | Super class descriptor |

Objects are allocated by a class'es constructor function with a 2-phase initialisation protocol:

* The first phase evaluates constructor args and invokes the pre-alloc hook, which initialises parameter and `let` fields, after possibly invoking the pre-alloc hook of the super class to do the same; this returns the values of all immutable fields (including constructor parameters as hidden fields).

* With these values as initialisation values, the instance struct is allocated.

* The second phase invokes the post-alloc hook, which evaluates expression declarations and `var` fields, after possibly invoking the post-alloc hook of the super class to do the same; this initialises var fields via mutation.

* Finally, the instance struct is returned.


### Generics

Generics require boxed types and use `eqref` as a universal representation for any value of variable type.

References returned from a generic function call are cast back to their concrete type when that type is known at the call site.

Moreover, arrays and tuples likewise represent all fields of boxed type with `eqref`, i.e., they are treated like generic types as well. This is necessary to enable passing them to generic functions that abstract some of their types, for example:
```
func fst<X, Y>(p : (X, Y)) : X { p.0 };

let p = ("foo", "bar");
fst<Text, Text>(p);
```
If `p` was not represented as `ref (struct eqref eqref)`, then the call to `fst` would produce invalid Wasm.


### Runtime type representation

All type parameters to a function or class are reified as value parameters of type `eqref`, representing a runtime description of the source-level type. Similarly, an object of generic class stores each of the class'es type parameter instantiations as hidden fields.

When invoking a generic function or constructor, a suitable representation is built dynamically for the type arguments (possibly using surrounding type parameters) and passed along.

The type representation is a fairly simple tree structure, where non-generic types are the leaves, which are a reference that is either an `i31ref` representing a primitive type (or a box thereof), or a reference to a class'es dispatch table representing that class. Generic types or any other structural types are represented by an array whose first slot is the tag, again an `i31ref` for built-in types or a reference to a class'es dispatch table, and the remaining slots are the representations of the type arguments.

| Wob type | Runtime type |
| -------- | ------------ |
| Bool     | i31(1)       |
| Byte     | i31(2)       |
| Int      | i31(3)       |
| Float    | i31(4)       |
| Text     | i31(5)       |
| Object   | i31(6)       |
| Bool$    | i31(-1)      |
| Byte$    | i31(-2)      |
| Int$     | i31(-3)      |
| Float$   | i31(-4)      |
| Text$    | [i31(7); i31(5)] |
| (Float$,Text) | [i31(8); i31(-4); i31(5)] |
| Object[] | [i31(9); i31(6)] |
| Object[]! | [i31(10); i31(6)] |
| C        | $disp_C      |
| C<Int$,Text> | array [$disp_C; i31(-3); i31(5)] |

Checking type equivalence is a simple parallel tree recursion, short-cut by reference equality. The runtime does not currently perform type canonicalisation.

Type definitions (with the `type` keyword) are implemented as functions returning a runtime type.

All runtime representations (including reified generic type parameters) are omitted in "parametric" compilation mode (command line flag `-p`). In that mode, casts are forbidden.


### Runtime system

Wob requires a tiny runtime system containing a handful of instrinsic operations, such as for `Text` type and for comparing runtime types. It is imported by each output module under the name `"wob-runtime".`And it comes in the form of a little Wasm module that is generated internally on the fly when using the interpreter.

When running outside the interpreter, the `"wob-runtime"` module has to be provided externally. A suitable standalone runtime module can be *generated* with the compiler invocation
```
wob -g wob-runtime.wasm
```

#### Headless mode

Using option `-n` when compiling sources, the compiler also allows producing *headless* Wasm modules that do not import a runtime. Instead they, include all necessary intrinisics in the produced module.


### Modules

Each Wob module compiles into a Wasm module. The body of a Wob module is compiled into the Wasm start function.

All global definitions are automatically turned into exports, of their respective [binding form](#bindings) (for simplicity, there currently is no access control). In addition, an exported global named `"return"` is generated for the program block's result value.

Import declarations directly map to Wasm imports of the same name. No other imports are generated for a module.


#### Linking

A Wob program can be executed by _linking_ its main module. Linking does not require any magic, it simply locates the [runime](#runtime-system) (if used) and all imported modules (by appending `.wasm` to the URL, which is interpreted as file path), recursively links them (using a simple registry to share instantiations), and maps exports to imports by name.


#### Batch compilation

The batch compiler inserts a custom section named `"wob-sig"` into the Wasm binary, which contains all static type information about the module. This is read back when compiling against an import of another module. (In principle, this information could also be stored in a separate file, since the Wasm code itself is not needed to compile an importing module.)


#### REPL

In the REPL, each input is compiled into a new module and [linked](#linking) immediately.

Furthermore, before compilation, each input is preprocessed by injecting imports from an implicit module named `"*env*"`, which represents the REPL's environment. That makes previous interactive definitions available to the module.


#### Running from JavaScript

Wob's linking model is as straightforward as it can get, and requires no language-specific support. It merely assumes that modules are loaded and instantiated in a bottom-up manner.

The simple template for runner glue code for node.js is provided in `js/wob.js` and shown below. With that, invoking
```
node js/wob.js name
```
suffices to run a compiled module `name.wasm`, provided the dependencies are avaliable in the right place. The Wob [runtime system](#runtime-system) is assumed to be found (as `wob-runtime.wasm`) in the current working directory (if not running headless), and imported modules (in compiled form) at their respective import paths, again relative to the current directory.

```
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
```
