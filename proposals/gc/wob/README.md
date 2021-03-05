# Wob -- Wasm Objects

An experimental language and implementation for exploring and evaluating the GC proposal.

### Overview

Wob is a typed mini-OO language in the style of C# and others. It is meant to be representative for the most relevant problems that arise when compiling such languages.

To that end, Wob features:

* primitive data types
* tuples and arrays
* functions and closures
* classes and inheritance
* first-class generics
* safe runtime casts
* simple modules

For simplicity, Wob omits various other common features, such as access control to classes and modules, more advanced control constructs, or sophisticated type inference, which are mostly independent from code generation and data representation problems. It also doesn't currently have interface types.

The `wob` implementation encompasses:

* Interpreter
* Compiler to Wasm (WIP)
* A read-eval-print-loop that can run either interpreted or compiled code

The language is fully implemented in the interpreter, but the compiler does not yet support closures, classes, and generics. It does, however, implement garbage-collected tuples, arrays, and text strings, already making use of many of the constructs in the GC proposal's MVP.


### Usage

#### Building

Saying
```
make
```
in the `wob` directory should produce a binary `wob` in that directory.

#### Invocation

The `wob` binary is both compiler and REPL. For example:

* `wob` starts the interactive prompt, using the interpreter.
* `wob -c` starts the interactive prompt, but each input is compiled and run via Wasm.
* `wob -r <file.wob>` batch-executes the file via the interpreter.
* `wob -r -c <file.wob>` batch-executes the file via Wasm.
* `wob -c <file.wob>` compiles the file to `<file.wasm>`.

See `wob -h` for further options.

Points of note:

* The Wasm code produced is self-contained with no imports (unless the source declares explicit imports of other Wob modules). Consequently, it can run in any Wasm environment supporting the GC proposal.

* That measn that there is no I/O. However, a program can communicate results via module exports or run assertions.

* When batch-executing, all Wasm code is itself executed via the Wasm reference interpreter, so don't expect performance miracles.


### Syntax

#### Types

```
typ ::=
  id ('<' typ,* '>')?                      named use
  '(' typ,* ')'                            tuple
  typ '[' ']'                              array
  ('<' id,* '>')? '(' typ,* ')' '->' typ   function
  typ '->' typ                             function (shorthand)
```

#### Expressions

```
unop  ::= '+' | '-' | '^' | '!'
binop ::= '+' | '-' | '*' | '/' | '%' | '&' | '|' | '^' | '<<' | '>>' | '#'
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
  exp ('<' typ,* '>')? '(' exp,* ')'       function call
  'new' id ('<' typ,* '>')? '(' exp,* ')'  class instantiation
  'new' typ '[' exp ']' '(' exp ')'        array instantiation
  exp ':' typ                              static type annotation
  exp ':>' typ                             dynamic type cast
  'assert' exp                             assertion
  'return' exp?                            function return
  block                                    block
  'if' exp block ('else' block)?           conditional
  'while' exp block                        loop
  'func' ('<' id,* '>')? '(' param,* ')'   anonymous function (shorthand)
      (':' typ) block
  'class' ('<' id,* '>')? '(' param,* ')'  anonymous class (shorthand)
      ('<:' id ('<' typ,* '>')? '(' exp,* ')')?
      block

block :
  '{' dec;* '}'                            block
```
There is no distinction between expressions and statements: a block can be used in any expression context and it evaluates to the value of its last expression, or `()` (the empty tuple) if its last `dec` isn't an expression.

An `assert` failure is indicated by executing an `unreachable` instruction in Wasm and thereby trapping.


#### Declarations
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
Classes have just one constructor, whose parameters are the definition's parameters and whose body is the class body. Inside class scope, immutable 'let' bindings can only refer to the class parameters or 'let' variables from the super-class, or any bindings from outer scope.


#### Modules
```
imp ::=
  'import' id? '{' id,* '}' 'from' text           import

module ::=
  imp;* dec;*
```
A module executes by executing all contained declarations in order. For simplicity, there is no access control beyond using blocks, that is, all top-level declarations are exported.

Imports are loaded eagerly and recursively. When an import specifies a qualifying identifier `M`, then all names from the import list are renamed to include the prefix `M_` -- this is a hack to avoid the introduction of name spacing constructs.


### Prebound Identifiers

#### Types
```
Bool  Byte  Int  Float  Text  Object
```

#### Values
```
true  false  null  nan  this
```
The `this` identifier is only bound within a class.


### Examples

#### Functions
```
func fac(x : Int) : Int {
  if x == 0 { return 1 };
  x * fac(x - 1);
};

assert fac(5) == 120;

func foreach<T>(a : T[], n : Int, f : T -> ()) {
  var i : Int = 0;
  while i < n {
    f(a[i]);
    i := i + 1;
  }
};

let a = [1, 2, 5, 6, -8];
var sum : Int = 0;
foreach<Int>(a, 5, func(k : Int) { sum := sum + k });
assert sum == 6;
```

#### Classes
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

#### Modules
```
// Module "intpair"
type Pair = (Int, Int);

func pair(x : Int, y : Int) : IntPair { (x, y) };
func fst(p : IntPair) : Int { p.0 };
func snd(p : IntPair) : Int { p.1 };
```
A client:
```
import IP {pair, fst} from "intpair";

let p = IP_pair(4, 5);
assert IP_fst(p) == 4;
```
