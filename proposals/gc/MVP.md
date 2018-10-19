# GC v1 Extensions

*Note: This design is still in flux!*

See [overview](Overview.md) for background.


## Language

Based on [reference types proposal](https://github.com/WebAssembly/reference-types), which introduces type `anyref` etc.

### Types

#### Value Types

* `eqref` is a new reference type
  - `reftype ::= ... | eqref`

* `ref <typeidx>` is a new reference type
  - `reftype ::= ... | ref <typeidx>`
  - `ref $t ok` iff `$t` is defined in the context

* `optref <typeidx>` is a new reference type
  - `reftype ::= ... | optref <typeidx>`
  - `optref $t ok` iff `$t` is defined in the context

* `i31ref` is a new reference type
  - `reftype ::= ... | i31ref`

* `rtt <reftype>` is a new reference type that is a runtime representation of type `<reftype>` (see [overview](Overview.md#casting-and-runtime-types))
  - `reftype ::= ... | rtt <reftype>`
  - `rtt t ok` iff `t ok`


#### Type Definitions

* `deftype` is a new category of types that generalises the existing type definitions in the type section
  - `deftype ::= <functype> | <structtype> | <arraytype>`
  - `module ::= {..., types vec(<deftype>)}`

* `structtype` describes a structure with statically indexed fields
  - `structtype ::= struct <fieldtype>*`

* `arraytype` describes an array with dynamically indexed fields
  - `arraytype ::= array <fieldtype>`

* `fieldtype` describes a struct or array field and whether it is mutable
  - `fieldtype ::= <mutability> <storagetype>`
  - `storagetype ::= <valtype> | <packedtype>`
  - `packedtype ::= i8 | i16`

* Unpacking a storage type yields `i32` for packed types, otherwise the type itself
  - `unpacked(t) = t`
  - `unpacked(pt) = i32`


#### Imports

* `type <typetype>` is an import description with an upper bound
  - `importdesc ::= ... | type <typetype>`
  - Note: `type` may get additional parameters in the future

* `typetype` describes the type of a type import, and is either an upper bound or a type equivalence
  - `typetype ::= sub <reftype> | eq <reftype>`

* Type imports have indices prepended to the type index space, similar to other imports.
  - Note: due to bounds, type imports can be mutually recursive with other type imports as well as regular type definitions. Hence they have to be validated together with the type section.


#### Exports

* `type <typeidx>` is an export description
  - `exportdesc ::= ... | type <typeidx>`
  - `type $t ok` iff `$t` is defined in the context


#### Subtyping

Greatest fixpoint (co-inductive interpretation) of the given rules (implying reflexivity and transitivity).

In addition to the rules for basic reference types:

* `eqref` is a subtype of `anyref`
  - `eqref <: anyref`
  - Note: `i31ref` and `funcref` are *not* a subtypes of `eqref`, i.e., those types do not expose reference equality

* `nullref` is a subtype of `eqref`
  - `nullref <: eqref`

* `i31ref` is a subtype of `anyref`
  - `i31ref <: anyref`
  - Note: `i31ref` is *not* a supertype of `nullref`, i.e., nut nullable

* Any nullable reference type is a subtype of `anyref` and a supertype of `nullref`
  - `optref $t <: anyref`
  - `nullref <: optref $t`

* Any concrete reference type is a subtype of the respective nullable reference type (and thereby of `anyref`)
  - `ref $t <: optref $t`
  - Note: concrete reference types are *not* supertypes of `nullref`, i.e., not nullable

* Any function reference type is a subtype of `funcref`
  - `ref $t <: funcref`
     - iff `$t = <functype>`

* Any optional reference type (and thereby respective concrete reference type) is a subtype of `eqref` if its not a function
  - `optref $t <: eqref`
     - if `$t = <structtype>` or `$t = <arraytype>`
     - or `$t = type rt` and `rt <: eqref`
  - TODO: provide a way to make data types non-eq, especially immutable ones

* Concrete and optional reference types are covariant
  - `ref $t1 <: ref $t2`
     - iff `$t1 <: $t2`
  - `optref $t1 <: optref $t2`
     - iff `$t1 <: $t2`

* Structure types support width and depth subtyping
  - `struct <fieldtype1>* <fieldtype1'>* <: struct <fieldtype2>*`
    - iff `(<fieldtype1> <: <fieldtype2>)*`

* Array types support depth subtyping
  - `array <fieldtype1> <: array <fieldtype2>`
    - iff `<fieldtype1> <: <fieldtype2>`

* Field types are covariant if they are immutable, invariant otherwise
  - `const <valtype1> <: const <valtype2>`
    - iff `<valtype1> <: <valtype2>`
  - `var <valtype> <: var <valtype>`
  - Note: mutable fields are *not* subtypes of immutable ones, so `const` really means constant, not read-only

* `rtt t` is a subtype of `anyref`
  - `rtt t <: anyref`
  - Note: `rtt t1` is *not* a subtype of `rtt t2`, even if `t1` is a subtype of `t2`; such subtyping would be unsound, since RTTs are used in both co- and contravariant roles (e.g., both when constructing and consuming a reference)


#### Defaultability

* Any numeric value type is defaultable

* A reference value type is defaultable if it is not of the form `ref $t`

* Locals must have a type that is defaultable.

* Table definitions with non-zero minimum size must have an element type that is defaultable. (Imports are not affected.)


### Instructions

#### Equality

* `ref.eq` compares two references whose types support equality
  - `ref.eq : [eqref eqref] -> [i32]`


#### Functions

* `ref.func` creates a function reference from a function index
  - `ref.func $f : [] -> (ref $t)`
     - iff `$f : $t`

* `call_ref` calls a function through a reference
  - `call_ref : [t1* (optref $t)] -> [t2*]`
     - iff `$t = [t1*] -> [t2*]`
  - traps on `null`


#### Structures

* `struct.new <typeidx>` allocates a structure of type `$t` and initialises its fields with given values
  - `struct.new $t : [t*] -> [(ref $t)]`
    - iff `$t = struct (mut t)*`
  - equivalent to `struct.new_rtt $t anyref (rtt.anyref)`

* `struct.new_rtt <typeidx> <reftype>` allocates a structure of type `$t` with RTT information and initialises its fields with given values
  - `struct.new_rtt $t t' : [(rtt t') t*] -> [(ref $t)]`
    - iff `$t = struct (mut t)*`
    - and `ref $t <: t'`

* `struct.new_default <typeidx>` allocates a structure of type `$t` and initialises its fields with default values
  - `struct.new_default $t : [] -> [(ref $t)]`
    - iff `$t = struct (mut t)*`
    - and all `t*` are defaultable

* `struct.get <typeidx> <fieldidx>` reads field `$x` from a structure
  - `struct.get $t i : [(optref $t)] -> [t]`
    - iff `$t = struct (mut1 t1)^i (mut ti) (mut2 t2)*`
    - and `t = unpacked(ti)`
  - traps on `null`

* `struct.set <typeidx> <fieldidx>` writes field `$x` of a structure
  - `struct.set $t i : [(optref $t) ti] -> []`
    - iff `$t = struct (mut1 t1)^i (var ti) (mut2 t2)*`
    - and `t = unpacked(ti)`
  - traps on `null`


#### Arrays

* `array.new <typeidx>` allocates an array of type `$t` and initialises its fields with a given value
  - `array.new $t : [t i32] -> [(ref $t)]`
    - iff `$t = array (mut t)`
  - equivalent to `array.new_rtt $t anyref (rtt.anyref)`

* `array.new_rtt <typeidx>` allocates a array of type `$t` with RTT information
  - `array.new_rtt $t t' : [(rtt t') t i32] -> [(ref $t)]`
    - iff `$t = array (mut t)`
    - and `ref $t <: t'`

* `array.new_default <typeidx>` allocates an array of type `$t` and initialises its fields with the default value
  - `array.new_default $t : [i32] -> [(ref $t)]`
    - iff `$t = array (mut t)`
    - and `t` is defaultable

* `array.get <typeidx>` reads an element from an array
  - `array.get $t : [(optref $t) i32] -> [t]`
    - iff `$t = array (mut t')`
    - and `t = unpacked(t')`
  - traps on `null`

* `array.set <typeidx>` writes an element to an array
  - `array.set $t : [(optref $t) i32 t] -> []`
    - iff `$t = array (var t')`
    - and `t = unpacked(t')`
  - traps on `null`

* `array.len <typeidx>` inquires the length of an array
  - `array.len $t : [(optref $t)] -> [i32]`
    - iff `$t = array (mut t)`
  - traps on `null`


#### Integer references

Tentatively, support a type of guaranteed unboxed scalars.
TODO: Is 31 bit value range the right choice?

* `i31ref.new` creates an `i31ref` from a 32 bit value, truncating high bit
  - `i31ref : [i32] -> [i31ref]`

* `i31ref.get_u` extracts the value, zero-extending
  - `i31ref.get_u : [i31ref] -> [i32]`

* `i31ref.get_s` extracts the value, sign-extending
  - `i31ref.get_s : [i31ref] -> [i32]`


#### Runtime Types

* `rtt.anyref` returns the RTT of type `anyref` as a subtype of only itself
  - `rtt.anyref : [] -> [(rtt anyref)]`

* `rtt.funcref` returns the RTT of type `funcref` as a subtype of `anyref`
  - `rtt.funcref : [] -> [(rtt funcref)]`

* `rtt.eqref` returns the RTT of type `eqref` as a subtype of `anyref`
  - `rtt.eqref : [] -> [(rtt eqref)]`

* `rtt.new <reftype> <reftype>` returns the RTT of the specified type as a subtype of a given RTT operand
  - `rtt.new t t' : [(rtt t')] -> [(rtt t)]`
    - iff `t <: t'`
  - multiple invocations of this instruction yield fresh RTTs

* All RTT instructions are considered *constant expressions*.


#### Casts

* `cast <reftype> <reftype>` casts a reference value down to a type given by a RTT representation
  - `cast t t' : [t (rtt t')] -> [t']`
     - iff `t' <: t <: anyref`
  - traps if the operand's (runtime) type is not defined to be a (transitive) subtype of `t`

* `br_on_cast <labelidx> <reftype> <reftype>` branches if a value can be cast down to a given reference type
  - `br_on_cast $l t t' : [t (rtt t')] -> [t]`
    - iff `t' <: t <: anyref`
    - and `$l : [t']`
  - passes cast operand along with branch


#### Local Bindings

* `let <valtype>* <blocktype> <instr>* end` locally binds operands to variables
  - `let t* bt instr* end : [t* t1*] -> [t2*]`
    - iff `bt = [t1*] -> [t2*]`
    - and `instr* : bt` under a context with `locals` extended by `t*` and `labels` extended by `[t2*]`


## Binary Format

TODO.


## JS API

See [GC JS API](MVP-JS.md).


## Questions

* Should RTT presence be made explicit in struct types and ref types?
  - for example, `(struct rtt ...)` and `rttref <: anyref`
  - only these types would be castable

* Provide a way to make data types non-eq, especially immutable ones?

* Allow closures into function reference types, via a `func.bind` operator?

* Should we rename `anyfunc` to `funcref` for more consistency?
