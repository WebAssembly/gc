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

For example, here is a short transcript of a REPL session with [`waml -c -x`](#invocation):
```
proposals/gc/waml$ ./waml -x -c
waml 0.1 interpreter
> val f x = x + 7;  f 5;
(module
  (type $0 (func))
  (type $1 (sub (struct (field i32))))
  (type $2 (sub 1 (struct (field i32) (field (ref 3)))))
  (type $3 (func (param (ref 2) (ref eq)) (result (ref eq))))
  (global $0 (mut (ref null 2)) (ref.null 2))
  (global $1 (mut i32) (i32.const 0))
  (func $0
    (type 0)
    (i32.const 1)
    (ref.func 1)
    (struct.new 2)
    (global.set 0)
    (global.get 0)
    (ref.as_non_null)
    (i32.const 5)
    (i31.new)
    (call 1)
    (ref.as_i31)
    (i31.get_s)
    (global.set 1)
  )
  (func $1
    (type 3)
    (local i32)
    (local.get 1)
    (ref.as_i31)
    (i31.get_s)
    (local.set 2)
    (local.get 2)
    (i32.const 7)
    (i32.add)
    (i31.new)
  )
  (export "return" (global 1))
  (export "f" (global 0))
  (export "func f" (func 1))
  (start 0)
  (elem $0 declare func 1)
)
12 : Int
val f : Int ->1 Int
> 
```
See [below](#under-the-hood) for some background on the produced code.


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

* The Wasm code produced is self-contained with no imports except the small Waml runtime system (unless the source declares explicit imports of other Waml modules). Consequently, it can run in any Wasm environment supporting the GC proposal.

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

### Paths
```
lpath :
  lid                                      plain
  upath '.' lid                            qualified

upath :
  uid                                      plain
  upath '.' uid                            qualified
```

### Types

```
typ ::=
  lid                                      variable
  upath typ*                               named use
  '(' typ,* ')'                            tuple
  typ '->' typ                             function
  'pack' sig                               first-class module
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
  'pack' mod ':' sig                       first-class module
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
  'rec' dec ('and' dec)*                   recursion
  'include' mod                            inclusion
```
Notes:

* The shorthand `exp` form without `'do'` is only allowed at the beginning of the program or after a semicolon.

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
  sig 'with' 'type' upath lid* '=' typ       type refinement
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
  'unpack' exp ':' sig                       unpacking first-class module
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
rec data Exp a =
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
rec data List a = Nil | Cons a (List a)

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
  rec data Set = Empty | Mem Elem Set Set

  val empty = Empty

  rec val add x s = case s of
    | Empty => Mem x Empty Empty
    | Mem y s1 s2 =>
      if Elem.lt x y then Mem y (add x s1) s2
      else if Elem.lt y x then Mem y s1 (add x s2)
      else s

  rec val mem x s = case s of
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
| (Float,Text)|ref (struct eqnnref eqnnref)| same   | same            |
| ref T     | ref (struct eqnnref) | same          | same            |
| C (nullary) | i31ref          | i31ref          | i31ref          |
| C (args)  | ref (struct i32 ...) | same         | same            |
| a         | ref eq            | ref eq          | ref eq          |
| T1 -> T2  | ref (struct i32 ...) | same         | same            |

Notably, all fields of tuples and the contents of ML type `ref` have to be represented as `(ref eq)`, in order to be compatible with [polymorphism](#polymorphism).


### Algebraic Data Types

The constructors of each date type are assigned numeric tags in alphabetical order. Their values are represented as either a `i31ref`, if the constructor has no arguments, or as a struct whose first field is the tag as an `i32`, and the remainder are the argument values.

The actual constructors have a first-class representation as well. For an argumentless constructor, it is the `i31ref` value itself, for others it is the cached RTT used for the value.

Pattern matching against an argumentless constructor simply tests for reference equality. Matching against another constructor first tries downcast to its type and if successful, checks the tag field.

When a constructor is applied to too few arguments, a [curried closure](#currying) is created.


### Polymorphism

Polymorphism requires the use of `anyref` as a universal representation for any value of variable type. In fact, the compiler uses `(ref eq)`, in order to allow direct comparisons for implementing equality on any type without an additional down cast.

References returned from a generic function call are cast back to their concrete type when that type is known at the call site.

Moreover, tuples and `ref` likewise represent all fields with `(ref eq)`, i.e., they are treated like polymorphic types as well. This is necessary to enable passing them to polymorphic functions that abstract some of their types, for example:
```
val f z (x, y) = x + y + z

val p = (3, 4)
val _ = f 2 p
```
If `p` was not represented as `ref (struct (ref eq) (ref eq))`, then the call to `f` would produce invalid Wasm.


### Bindings

Waml bindings are compiled to Wasm as follows.

| Waml declaration | in global scope | in local scope | in struct scope |
| ---------------- | --------------- | -------------- | --------------- |
| `val`            | mutable `global`| `local`        | immutable field |
| `module`         | mutable `global`| `local`        | immutable field |

Note that all global declarations have to be compiled into mutable globals, since they could not be initialised otherwise. Also, globals need to be of nullable type.

The compiler can be configured (independently form each other) to either box or unbox values stored in locals, globals, temporaries or for pattern scrutinees (run with `-h` for flags).


### Functions and Closures

Functions are represented as flat closures. In order to support currying, each closure also carries the function's defined arity. Hence, closures map to Wasm structs with the following layoug:

| Index | Type | Description |
| ----- | ---- | ----------- |
| 0     | i32  | Arity       |
| 1     | ref (func ...) | Code pointer |
| 2     | ...  | 1st captured environment value |
| 3     | ...  | 2nd captured environment value |
| ...   | ...  | ... |

All fields in a closure are immutable, with the only exception of environment fields for bindings within the same recursive declaration group. This is so that the necessary mutually recursive closures can be constructed, by fixing up the respective slots after all other closures in the group have been allocated.

Code pointers are references to the actual Wasm function. In addition to its regular parameters, its first parameter is a reference to its a closure environment. However, in order to be compatible across call sites, the closure parameter's type does not include the function-specific environment fields. It hence has to be down-cast first inside the function to access the environment fields.

In order to avoid an infinite number of cases for [currying](#currying), there is a maximum arity `M` for which parameters are passed directly. Beyond that treshold, they are wrapped in a variadic array.

Overall, this scheme creates a hierarchy of closure types as follows:
```
$anyclos               = (struct (field i32))
 +- $clos1             = (struct (field i32(1) (ref $code1)))
 |   +- $clos1/i32     = (struct (field i32(1) (ref $code1) i32))
 |   +- $clos1/f64-i32 = (struct (field i32(1) (ref $code1) f64 i32))
 |   ...
 +- $clos2             = (struct (field i32(2) (ref $code2)))
 |   ...
 +- $clos3             = (struct (field i32(3) (ref $code3)))
 |   ...
 .
 .
 +- $closM             = (struct (field i32(M) (ref $codeM)))
 |   ...
 +- $closVar           = (struct (field i32(N>M) (ref $codeVar)))
     ...
```
where
```
$code1 = (func (param (ref $clos1) (ref eq)) (result (ref eq)))
$code2 = (func (param (ref $clos2) (ref eq) (ref eq)) (result (ref eq)))
$code3 = (func (param (ref $clos3) (ref eq) (ref eq) (ref eq)) (result (ref eq)))
...
$codeM = (func (param (ref $clos3) (ref eq) (ref eq) ... (ref eq)) (result (ref eq)))
$codeVar = (func (param (ref $clos3) (ref $argv)) (result (ref eq)))
$argv = (array (ref eq))
...
```
For example, the Waml function `f` in the following example,
```
val a = 5
module M = {val b = 7}

val f x y = x + y + a + M.b
```
has this Wasm representation:
```
;; Generic code and closure types for binary functions
(type $code/2 (func (param (ref $clos/2) (ref eq) (ref eq)) (result (ref eq))))
(type $clos/2 (sub $anyclos (struct (field i32 (ref $code/2)))))

;; Closure type for f
(type $clos/f (sub $clos/2 (struct (field i32 (ref $code/2) i31ref (ref $M)))))

(func $f (param $clos (ref $clos/2)) (param $x (ref eq)) (param $y (ref eq)) (result (ref eq))
  (local $clos/f)
  (local.get $clos)
  (ref.cast)
  (local.set $clos/f)
  ;; actual body
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


### Type Inference

The Waml compiler implements full Damas/Milner polymorphic type inference, with minor extension for dealing with overlading resolution for arithmetic operators. In addition, it implements module-level type checking using the "F-ing modules" approach.

While certainly interesting, this is fairly standard and largely orthogonal to targetting Wasm, so we omit the details here.


### ML-style Modules

Waml implements a complete ML-style module system, where a module is either a _structure_, encapsulating a set of definitions, or a _functor_, which is a module parameterised over another module. Both kinds of modules can both be nested into structures and passed to or returned from functors. In other words, modules are higher-order.

Each Waml structure is compiled to a corresponding Wasm struct carrying the definition it exports. Because any type aspect of a module signature can be made abstract after the fact (using signature annotations), which provides a module-level form of [polymorphism](#polymorphism), all structure fields representing values also need to use `(ref eq)` as a [universal representation](#polymorphism).

Functors are compiled to functions. Since they can be defined in nested scopes, they have to be represented as _closures_, in the same way as [regular functions](#functions-and-closures).

Signature subtyping is implemented by coercions. In the higher-order case, i.e., on functors, this requires generating suitable wrapper closures performing the coercions on argument and result upon application.


### Compilation Units

Each Waml file compiles into a Wasm module. The body of a Waml unit is compiled into the Wasm start function.

All global definitions from the source program are automatically turned into exports. All these exports are ([mutable](#bindings)) globals, which for functions contains the respective closure. Functions defined in directly in the toplevel scope are additionally exported as Wasm function under the same name prefixed with `"func "`, so that they can be invoked directly (though for types to match up, this still requires passing them a dummy closure environment). In addition, an exported global named `"return"` is generated for the program block's result value.

ML Modules defined in a unit are likewise exported as globals. Their export name is prefixed by `"module "` to accompany for the name spacing separation.

Import declarations in a unit compile to a list of Wasm imports for all exports of the imported module. These are implcitly bundled into a structure module at the import side. No other imports are generated for a compilation unit.


#### Linking

A Waml program can be executed by _linking_ its main module. Linking does not require any magic, it simply locates the [runime](#runtime-system) (if used) and all imported modules (by appending `.wasm` to the URL, which is interpreted as file path), recursively links them (using a simple registry to share instantiations), and maps exports to imports by name.


#### Batch compilation

The batch compiler inserts a custom section named `"waml-sig"` into the Wasm binary, which contains all static type information about the module. This is read back when compiling against an import of another module. (In principle, this information could also be stored in a separate file, since the Wasm code itself is not needed to compile an importing module.)


#### REPL

In the REPL, each input is compiled into a new module and [linked](#linking) immediately.

Furthermore, before compilation, each input is preprocessed by injecting imports from an implicit module named `"*env*"`, which represents the REPL's environment. That makes previous interactive definitions available to the module.


#### Running from JavaScript

Waml's linking model is as straightforward as it can get, and requires no language-specific support. It merely assumes that modules are loaded and instantiated in a bottom-up manner.

The simple template for runner glue code for node.js is provided in `js/wob.js` and shown below. With that, invoking
```
node js/waml.js name
```
suffices to run a compiled module `name.wasm`, provided the dependencies are avaliable in the right place. The Waml [runtime system](#runtime-system) is assumed to be found (as `waml-runtime.wasm`) in the current working directory (if not running headless), and imported modules (in compiled form) at their respective import paths, again relative to the current directory.
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
```
