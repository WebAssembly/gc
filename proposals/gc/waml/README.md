# Waml -- Wasm ML

An experimental functional language and implementation for exploring and evaluating the Wasm [GC proposal](https://github.com/WebAssembly/gc/#gc-proposal-for-webassembly).

## Overview

Waml is a typed FP language in the style of ML and friends. It is meant to be representative of the most relevant problems that arise when compiling such languages to Wasm with GC extensions. These arguably are:

* currying
* polymorphism
* algebraic data types
* higher-order modules
* separate compilation

To that end, Waml is a complete implementation of an ML dialect, providing all major features of the ML family of languages:

* primitive data types
* functions, closures, and currying
* algebraic data types and pattern matching
* references
* polymorphic type inference
* higher-order modules and sealing
* compilation units with separate compilation and client-side linking

For simplicity, Waml omits various other common features, such as user-defined operators, records, type classes, or more sophisticated type system features, which are mostly independent from code generation and data representation problems.

The `waml` implementation encompasses:

* Interpreter
* Compiler to Wasm
* A read-eval-print-loop that can run either interpreted or compiled code

The compiler makes use of [most of the constructs](#under-the-hood) in the GC proposal's MVP.


## Usage

### Building

Saying
```
make
```
in the `waml` directory should produce a binary `waml` in that directory.

### Invocation

The `waml` binary is both compiler and REPL. For example:

* `waml` starts the interactive prompt, using the interpreter.
* `waml -c` starts the interactive prompt, but each input is compiled and run via Wasm.
* `waml -c -x` same, but the generated Wasm code is also shown for each input.
* `waml -r <file.waml>` batch-executes the file via the interpreter.
* `waml -r -c <file.waml>` batch-executes the file via Wasm.
* `waml -c <file.waml>` compiles the file to `<file.wasm>`.

See `waml -h` for further options.

Points of note:

* The Wasm code produced is self-contained with no imports (unless the source declares explicit imports of other Waml modules). Consequently, it can run in any Wasm environment supporting the GC proposal.

* That measn that there is no I/O. However, a program can communicate results via module exports or run assertions.

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

### Paths
```
lpath :
  lid                                      plain
  upath '.' lid                            qualified

upath :
  lid                                      plain
  upath '.' uid                            qualified
```

### Types

```
typ ::=
  lid                                      variable
  upath typ*                               named use
  '(' typ,* ')'                            tuple
  typ '->' typ                             function
```
Note:

* `lid` denotes identifiers starting with lower case or `_`, while `uid` denotes identifiers starting with upper case.


### Expressions

```
unop  ::= '+' | '-' | '^' | '~'
binop ::= '+' | '-' | '*' | '/' | '%' | '&&' | '||' | '^^' | '<<' | '>>' | '#'
relop ::= '==' | '<>' | '<' | '>' | '<=' | '>='
logop ::= '/\' | '\/'

lit ::=
  int                                      integer
  float                                    floating-point
  text                                     text

exp ::=
  lit                                      literal
  upath                                    constructor
  lpath                                    variable use
  unop exp                                 unary operator
  exp binop exp                            binary operator
  exp relop exp                            comparison operator
  exp logop exp                            logical operator
  'ref' exp                                reference
  exp '!'                                  dereference
  exp ':=' exp                             assignment
  '(' exp,* ')'                            tuple
  exp '::' exp                             list cons (shorthand)
  '[' exp,* ']'                            list (shorthand)
  'fun' pat+ '=>' exp                      function
  exp exp                                  function call
  exp ':' typ                              type annotation
  'if' exp 'then' exp ('else' exp)?        conditional
  'case' exp 'of' case|*                   case
  'let' dec;* 'in' exp                     local declaration
  '(' dec;* ')'                            sequencing (shorthand)

case :
  pat '=>' exp

pat :
  '_'                                      wildcard
  lit                                      literal
  lid                                      variable
  upath pat*                               constructor
  'ref' pat                                reference
  '(' pat,* ')'                            tuple
  pat '::' pat                             list cons (shorthand)
  '[' pat,* ']'                            list (shorthand)
  pat ':' typ                              type annotation
```
Note:

* The operators `&&`, `||`, and `^^` are bitwise integer operators, the boolean ones are spelled `/\`, `\/`, and `~`.

* The semicolons between `dec` are optional.


### Declarations
```
dec ::=
  exp                                      expression (shorthand for `do`)
  'do' exp                                 expression
  'assert' exp                             assertion
  'val' pat '=' exp                        pattern binding
  'val' lid pat+ (':' typ)? '=' exp        function (shorthand)
  'type' uid lid* '=' typ                  type
  'data' uid lid* '=' (uid typ*)|*         algebraic data type
  'module' uid ('(' uid ':' sig ')')* (':' sig)? '=' mod     module
  'signature' uid '=' sig                  signature
  'rec' dec (and' dec)*                    recursion
  'include' mod                            inclusion
```
Notes:

* The shorthand `exp` form without `do` is only allowed at the beginning of the program or after a semicolon.

* An `assert` failure is indicated by executing an `unreachable` instruction in Wasm and thereby trapping.

* The declarations inside a `rec` block must either be all function bindings or all data bindings.


### Signatures
```
spec ::=
  'val' lid ':' typ                          value
  'type' uid lid* ('=' typ)?                 type
  'data' uid lid* '=' (uid typ*)|*           algebraic data type
  'module' uid ':' sig                       module
  'signature' uid '=' sig                    signature
  'rec' spec ('and' spec)*                   recursion
  'include' sig                              inclusion

sig ::=
  upath                                      named use
  '{' spec;* '}'                             structure
  '(' uid ':' sig ')' -> sig                 functor
  sig -> sig                                 functor (shorthand)
  sig 'with' 'type' upath '=' typ            refinement
```
Notes:

* The semicolons between `spec` are optional.

* The specifications inside a `rec` block must all be data bindings.


### Modules
```
mod ::=
  upath                                      named use
  '{' dec;* '}'                              structure
  'fun' '(' uid ':' sig ')' '=>' mod         functor
  mod mod                                    functor call
  mod ':' sig                                signature annotation
  'let' dec;* 'in' mod                       local declaration
```
Note:

* The semicolons between `dec` are optional.


### Programs
```
imp ::=
  'import' uid 'from' text                 import

prog ::=
  imp;* dec;*
```

Notes:

* The semicolons between `imp` or `dec` are optional.

* A program executes by executing all contained declarations in order.

* Imports are loaded eagerly and recursively. The body of a program is treated as a structure for the sake of importing it from another module.

* With batch compilation, modifying a module generally requires recompiling its dependencies, otherwise Wasm linking may fail.


### Prebound Identifiers

#### Types
```
Bool  Byte  Int  Float  Text
```

#### Values
```
True  False  nan
```


## Examples

### Functions
```
val sqr x = x*x

assert sqr 5 == 25
```
```
rec val fac x = if x == 0 then 1 else x * fac (x-1)

assert fac 5 == 120
```

### Pattern Matching
```
data Exp a =
  | Lit a
  | Add (Exp a) (Exp a)
  | Mul (Exp a) (Exp a)

rec val eval (e : Exp Float) =
  case e of
  | Lit x => x
  | Add e1 e2 => eval e1 + eval e2
  | Mul e1 e2 => eval e1 * eval e2

val exp = Add (Lit 3.1) (Mul (Add (Lit 1.2) (Lit 2.0)) (Lit (-3.0)))
val x = eval exp
```

### Polymorphism
```
data List a = Nil | Cons a (List a)

rec val foldl xs y f =
  case xs of
  | Nil => y
  | Cons x xs' => foldl xs' (f x y) f

val l = [1, 2, 5, 6, -8]
val sum = foldl l 0 (fun i sum => sum + i)
assert sum == 6
```

### Parameterised Modules
```
signature Set =
{
  type Elem
  type Set
  val empty : Set
  val add : Elem -> Set -> Set
  val mem : Elem -> Set -> Bool
}

signature Ord =
{
  type T
  val lt : T -> T -> Bool
}

module MakeSet (Elem : Ord) : Set with type Elem = Elem.T =
{
  type Elem = Elem.T
  data Set = Empty | Mem Elem Set Set

  val empty = Empty

  rec val add x s =
    case s of
    | Empty => Mem x Empty Empty
    | Mem y s1 s2 =>
      if Elem.lt x y then Mem y (add x s1) s2
      else if Elem.lt y x then Mem y s1 (add x s2)
      else s

  rec val mem x s =
    case s of
    | Empty => False
    | Mem y s1 s2 =>
      if Elem.lt x y then mem x s1 else ~ Elem.lt y x \/ mem x s2
}

module IS = MakeSet {type T = Int; val lt x y = x < y}
val s = IS.add 3 (IS.add 1 (IS.add 3 (IS.add 5 IS.empty)))
```

### Separate Compilation
```
;; Module "pair"
type Pair a b = (a, b)

val pair x y = (x, y)
val fst (x, _) = x
val snd (_, y) = y
```
A client:
```
import Pair from "pair"

let p = Pair.pair 4 5
assert Pair.fst p == 4
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
br_on_data  br_on_cast
i31.new  i31.get_u
struct.new  struct.get  struct.get_u  struct.set
array.new  array.new_default  array.get  array.get_u  array.set  array.len
rtt.canon  rtt.sub
```

(Currently unused are the remaining `ref.is_*`, `ref.as_*`, and `br_on_*` instructions, `ref.test`, the signed `*.get_s` instructions, and `struct.new_default`.)


### Value representations

Waml types are lowered to Wasm as shown in the following table.

| Waml type | Wasm unboxed type | Wasm boxed type | Wasm field type |
| --------- | ----------------- | --------------- | --------------- |
| Bool      | i32               | i31ref          | i8              |
| Byte      | i32               | i31ref          | i8              |
| Int       | i32               | i31ref          | i32             |
| Float     | f64               | ref (struct f64)| f64             |
| Text      | ref (array i8)    | same            | same            |
| (Float,Text)|ref (struct anyref anyref)| same   | same            |
| ref T     | ref (struct anyref) | same          | same            |
| C (nullary) | i31ref          | i31ref          | i31ref          |
| C (args)  | ref (struct i32 ...) | same         | same            |
| a         | anyref            | anyref          | anyref          |
| T1 -> T2  | ref (struct i32 ...) | same         | same            |

Notably, all fields of tuples and the contents of type `ref` have to be represented as `anyref`, in order to be compatible with [polymorphism](#polymorphism).


### Polymorphism

Polymorphism requires the use of `anyref` as a universal representation for any value of variable type.

References returned from a generic function call are cast back to their concrete type when that type is known at the call site.

Moreover, tuples and `ref` likewise represent all fields with `anyref`, i.e., they are treated like polymorphic types as well. This is necessary to enable passing them to polymorphic functions that abstract some of their types, for example:
```
val f z (x, y) = x + y + z

val p = (3, 4)
val _ = f 2 p
```
If `p` was not represented as `ref (struct anyref anyref)`, then the call to `f` would produce invalid Wasm.


### Bindings

Waml bindings are compiled to Wasm as follows.

| Waml declaration | in global scope | in local scope | in struct scope |
| ---------------- | --------------- | -------------- | --------------- |
| `val`            | mutable `global`| `local`        | immutable field |
| `module`         | mutable `global`| `local`        | immutable field |

Note that all global declarations have to be compiled into mutable globals, since they could not be initialised otherwise.


### Module representations

Each Waml structure is compiled into a corresponding Wasm struct.

Parameterised modules are compiled to functions. Since they can be defined locally, they are actually represented as _closures_, in the same way as [core-level closures](#functions-and-closures).

Signature subtyping is implemented by coercions. In the higher-order case, i.e., on parameterised modules, this requires generating suitable wrapper closures performing the coercions on argument and result upon application.


### Functions and Closures

Functions are represented as flat closures. In order to support currying, each closure also carries the function's defined arity. Hence, closures map to Wasm structs with the following layoug:

| Index | Type | Description |
| ----- | ---- | ----------- |
| 0     | i32  | Arity       |
| 1     | ref (func ...) | Code pointer |
| 2     | ...  | 1st captured environment value |
| 3     | ...  | 2nd captured environment value |
| ...   | ...  | ... |

Code pointers are references to the actual function. In addition to its regular parameters, its first parameter is a reference to its a closure environment. However, in order to be compatible across call sites, this is typed without the environment fields, and hence has to be downcast in the function to access the environment.

For example, the Waml function `f` in the following example,
```
val a = 5
module M = {val b = 7}

val f x y = x + y + a + M.b
```
has this Wasm representation:
```
;; Generic code and closure types for binary functions
(type $code/2 (func (param (ref $clos/2) anyref anyref) (result anyref)))
(type $clos/2 (struct (field i32 (ref $code/2))))

;; Closure type for f
(type $clos/f (struct (field i32 (ref $code/2) i31ref (ref $M))))
(global $rtt-clos/f ...)

(func $f (param $clos (ref $clos/2)) (param $x anyref) (param $y anyref) (result anyref)
  (local.get $clos)
  (global.get $rtt-clos/f)
  (rtt.cast)
  (let (local $clos/f)
    ;; actual body
  )
)
```

### Currying

The compiler implements the so-called _eval/apply_ technique for currying.

When the function called is statically known at a call site, and applied to the appropriate number of parameters, it is compiled into a direct call.

However, due to the combination of first-class functions, currying, and polymorphism in a functional language, the callen is not generally known, nor is its physical arity. A call may be both under-applying and over-applying. For example, consider:
```
val add1 x = let val f y = x + y in f
val add2 x y = x + y
val add3 x y z = x + y + z

val call f = f 1 2  ;; call : (Int -> Int -> a) -> a has polymorphic result type

do call add1    ;; => add1 1 2 over-applies
do call add2    ;; => add2 1 2
do call add3 3  ;; => add3 1 2 under-applies

```
To handle these different cases, it generally is necessary to perform two-dimensional dispatch on both the call and the callee arity. The former is known statically, but the latter isn't.

To this end, a call to an unknown target is compiled to a call to an auxiliary`apply` combinator of the given arity. This function then dispatches on the actual arity of the callee (reading it off the closure). When the number of arguments matches, it just forwards the call. When over-applied, it splits the call into two consecutive calls, with the first one forwarding the expected number of arguments, and the second recursively passing the resulting closure to another `apply` combinator of respective lower arity. When under-applied, it allocates an internal closure binding the supplied arguments whose code recursively forwards a call to `apply` (this time of higher arity) once called with an extra argument.

The `apply` combinators are part of the runtime. However, since these combinators mutually depend on those of both lower and higher arity, there has to be a maximum arity that is handled this way. Once reached, arguments are passed as an array instead. The apply combinator can handle the array case generically.


### Compilation Units

Each Waml file compiles into a Wasm module. The body of a Waml unit is compiled into the Wasm start function.

All global definitions from the source program are automatically turned into exports, of their respective [binding form](#bindings) (for simplicity, there currently is no access control). In addition, an exported global named `"return"` is generated for the program block's result value.

Import declarations compile to a list of imports for all all exports of the imported module. These are implcitly bundled into a structure at the import side. No other imports are generated for a compilation unit.


#### Linking

A Waml program can be executed by _linking_ its main unit. Linking does not require any magic, it simply locates all imported Wasm modules (by appending `.wasm` to the URL, which is interpreted as file path), recursively links them (using a simple registry to share instantiations), and maps exports to imports by name.


#### Batch compilation

The batch compiler inserts a custom section named `"waml-sig"` into the Wasm binary, which contains all static type information about the module. This is read back when compiling against an import of another module. (In principle, this information could also be stored in a separate file, since the Wasm code itself is not needed to compile an importing module.)


#### REPL

In the REPL, each input is compiled into a new module and [linked](#linking) immediately.

Furthermore, before compilation, each input is preprocessed by injecting imports from an implicit module named `"*env*"`, which represents the REPL's environment. That makes previous interactive definitions available to the module.


#### Running from JavaScript

Waml's linking model is as straightforward as it can get, and requires no language-specific support. It merely assumes that modules are loaded and instantiated in a bottom-up manner.

Here is a template for minimal glue code to run Waml programs in an environment like node.js. Invoking `run("name")` should suffice to run a compiled `name.wasm` and return its result, provided the dependencies are also avaliable in the right place.
```
'use strict';

let fs = require('fs').promises;

function arraybuffer(bytes) {
  let buffer = new ArrayBuffer(bytes.length);
  let view = new Uint8Array(buffer);
  for (let i = 0; i < bytes.length; ++i) {
    view[i] = bytes.charCodeAt(i);
  }
  return buffer;
}

let registry = {};

async function link(name) {
  let bytes = await fs.readFile(name + ".wasm", "binary");
  let binary = arraybuffer(bytes);
  let module = await WebAssembly.compile(binary);
  for (let im of WebAssembly.Module.imports(module)) {
    link(im.module);
  }
  let instance = await WebAssembly.instantiate(module, registry);
  registry[name] = instance.exports;
  return instance;
}

async function run(name) {
  let instance = await link(name);
  return instance.return;
}
```
