# GC v1 Extensions

*Note: This design is still in flux!*

See [overview](Overview.md) for background.

The functionality provided with this first version of GC support for Wasm is intentionally limited in the spirit of a "a minimal viable product" (MVP).
As a rough guideline, it includes only essential functionality and avoids features that may provide better performance in some cases, but whose lack can be worked around in a reasonable manner.

In particular, it is expected that compiling to this minimal functionality will require a substantial number of runtime casts that may be eliminated by future extensions.
A range of such extensions are discussed in the [Post-MVP](Post-MVP.md) document.
Most of them are expected to be added before GC support can be considered reasonably "complete".


## Language

Based on the following proposals:

* [reference types](https://github.com/WebAssembly/reference-types), which introduces reference types

* [typed function references](https://github.com/WebAssembly/function-references), which introduces typed references `(ref null? $t)` etc.

* [type imports](https://github.com/WebAssembly/proposal-type-imports), which allows type definitionss to be imported and exported

All three proposals are prerequisites.


### Types

#### Heap Types

[Heap types](https://github.com/WebAssembly/function-references/blob/master/proposals/function-references/Overview.md#types) classify the target of a reference and are extended:

* `any` is a new heap type
  - `heaptype ::= ... | any`
  - the common supertype of all referenceable types

* `eq` is a new heap type
  - `heaptype ::= ... | eq`
  - the common supertype of all referenceable types on which comparison (`ref.eq`) is allowed

* `i31` is a new heap type
  - `heaptype ::= ... | i31`
  - the type of unboxed scalars

* Note: heap types `func` and `extern` already exist via [reference types proposal](https://github.com/WebAssembly/reference-types), and `(ref null? $t)` via [typed references](https://github.com/WebAssembly/function-references)


#### Reference Types

New abbreviations are introduced for reference types in binary and text format, corresponding to `funcref` and `externref`:

* `anyref` is a new reference type
  - `anyref == (ref null any)`

* `eqref` is a new reference type
  - `eqref == (ref null eq)`

* `i31ref` is a new reference type
  - `i31ref == (ref i31)`


#### Value Types

* `rtt <n> <heaptype>` is a new value type that is a runtime representation of the static type `<heaptype>` and has `n` dynamic supertypes (see [Runtime types](#runtime-types))
  - `valtype ::= ... | rtt <n> <heaptype>`
  - `rtt n t ok` iff `t ok`


#### Type Definitions

* `deftype` is a new category of types that generalises the existing type definitions in the type section
  - `deftype ::= <functype> | <structtype> | <arraytype>`
  - `module ::= {..., types vec(<deftype>)}`

* `structtype` describes a structure with statically indexed fields
  - `structtype ::= struct <fieldtype>*`

* `arraytype` describes an array with dynamically indexed fields
  - `arraytype ::= array <fieldtype>`
  - Note: in the MVP, all arrays must be defined as mutable

* `fieldtype` describes a struct or array field and whether it is mutable
  - `fieldtype ::= <mutability> <storagetype>`
  - `storagetype ::= <valtype> | <packedtype>`
  - `packedtype ::= i8 | i16`

* Unpacking a storage type yields `i32` for packed types, otherwise the type itself
  - `unpacked(t) = t`
  - `unpacked(pt) = i32`


#### Subtyping

Greatest fixpoint (co-inductive interpretation) of the given rules (implying reflexivity and transitivity).

##### Heap Types

In addition to the [existing rules](https://github.com/WebAssembly/function-references/proposals/function-references/Overview.md#subtyping) for heap types:

* every type is a subtype of `any`
  - `t <: any`

* `i31ref` is a subtype of `eqref`
  - `i31 <: eq`

* Any concrete type is a subtype of `eq` if its not a function
  - `(type $t) <: eq`
     - if `$t = <structtype>` or `$t = <arraytype>`
     - or `$t = type rt` and `rt <: eq` (imports)
  - TODO: provide a way to make data types non-eq, especially immutable ones


#### Value Types

* `rtt n t` is a subtype of `any`
  - `rtt n t <: any`
  - Note: `rtt n t1` is *not* a subtype of `rtt n t2`, even if `t1` is a subtype of `t2`; such subtyping would be unsound, since RTTs are used in both co- and contravariant roles (e.g., both when constructing and consuming a reference)


##### Defined Types

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


### Runtime

#### Runtime Types

* Runtime types (RTTs) are explicit values representing types at runtime; a value of type `rtt <n> <heaptype>` is a dynamic representative of static type `<heaptype>`.

* All RTTs are explicitly created and all operations involving dynamic type information (like casts) operate on explicit RTT operands.

* There is a runtime subtyping hierarchy on RTTs; creating an RTT requires providing a *parent type* in the form of an existing RTT; the RTT for `anyref` is the root of this hierarchy.

* An RTT value t1 is a *sub-RTT* of another RTT value t2 iff either of the following holds:
  - t1 and t2 represent the same static type, or
  - t1 has a parent that is a sub-RTT of t2.

* The count `<n>` in the static type of an RTT value denotes the length of the supertype chain, i.e., its "inheritance depth" (not counting `anyref`, which always is at the top). This information enables efficient implementation of runtime casts in an engine.

* Validation requires that each parent type is a representative of a static supertype of its child; runtime subtyping hence is a sub-relation of static subtyping (a graph with fewer nodes and edges).

* At the same time, runtime subtyping forms a linear hierarchy such that the relation can be checked efficiently using standard implementation techniques (the runtime subtype hierarchy is a tree-shaped graph).

Note: RTT values correspond to type descriptors or "shape" objects as they exist in various engines. Moreover, runtime casts along the hierachy encoded in these values can be implemented in an engine efficiently by including a vector of its (direct and indirect) super-RTTs in each RTT value (with itself as the last entry). The value `<n>` then denotes the length of this vector. A subtype check between two RTT values can be implemented as follows using such a representation. Assume RTT value v1 has static type `(rtt n1 t1)` and v2 has type `(rtt n2 t2)`. To check whether v1 denotes a sub-RTT of v2, first verify that `n1 >= n2`. Then compare v2 to the n2-th entry in v1's supertype vector. If they are equal, v1 is a sub-RTT. For casts, the static type of v1 (taken from the object to cast) is not known at compile time, so `n1 >= n2` becomes a dynamic check as well.

Example: Consider three types and corresponding RTTs:
```
(type $A (struct))
(type $B (struct (field i32)))
(type $C (struct (field i32 i64)))

(global $rttA (rtt 1 $A) (rtt.sub $A (rtt.canon any)))
(global $rttB (rtt 2 $B) (rtt.sub $B (global.get $rttA)))
(global $rttC (rtt 3 $C) (rtt.sub $C (global.get $rttB)))
```
Here, `$rttA` would carry supertype vector `[$rttA]`, `$rttB` has `[$rttA, $rttB]`, and `$rttC` has `[$rttA, $rttB, $rttC]`.

Now consider a function that casts a `$B` to a `$C`:
```
(func $castBtoC (param $x (ref $B)) (result (ref $C))
  (ref.cast (local.get $x) (global.get $rttC))
)
```
This can compile to machine code that (1) reads the RTT from `$x`, (2) checks that the length of its supertype table is >= 3, and (3) pointer-compares table[2] against `$rttC`.


#### Values

* Creating a structure or array optionally allows supplying a suitable RTT value to represent its runtime type; it is `any` if none is given.

* Each reference value has an associated runtime type:
  - For structures or arrays, it is the RTT value provided upon creation, or `anyref` if none.
  - For functions, it is the RTT value for the function's type.
  - For `i31ref` references it is the RTT value for `i31ref`.

* The so-defined runtime type is the only type information that can be discovered about a reference value at runtime; a structure or array with RTT `any` thereby is fully opaque to runtime type checks (and an implementation may choose to optimize away its RTT).

#### Failure

Allocation of memory objects may fail for implementation-specific reasons, such as system resource exhaustion or a host-defined limit, or being unable to fit a large array in available address space.

Similar to stack overflow, allocation failure may materialise in an implementation-dependent way, such as trapping or terminating the host process. Implementors should be aware this may be used as a denial of service vector.

### Instructions

#### Equality

* `ref.eq` compares two references whose types support equality
  - `ref.eq : [eqref eqref] -> [i32]`


#### Functions

Perhaps add the following short-hands:

* `ref.is_func` checks whether a reference is a function
  - `ref.is_func : [anyref] -> [i32]`
  - equivalent to `(rtt.canon func) (ref.test)`

* `ref.as_func` converts to a function reference
  - `ref.as_func : [anyref] -> [funcref]`
  - traps if reference is not a function
  - equivalent to `(rtt.canon func) (ref.cast)`


#### Structures

* `struct.new_with_rtt <typeidx>` allocates a structure with RTT information determining its [runtime type](#values) and initialises its fields with given values
  - `struct.new_with_rtt $t : [t'* (rtt n $t)] -> [(ref $t)]`
    - iff `$t = struct (mut t')*`
  - allocation failure behavior is [implementation-defined](#failure)

* `struct.new_default_with_rtt <typeidx>` allocates a structure of type `$t` and initialises its fields with default values
  - `struct.new_default_with_rtt $t : [(rtt n $t)] -> [(ref $t)]`
    - iff `$t = struct (mut t')*`
    - and all `t'*` are defaultable
  - allocation failure behavior is [implementation-defined](#failure)

* `struct.get_<sx>? <typeidx> <fieldidx>` reads field `i` from a structure
  - `struct.get_<sx>? $t i : [(ref null $t)] -> [t]`
    - iff `$t = struct (mut1 t1)^i (mut ti) (mut2 t2)*`
    - and `t = unpacked(ti)`
    - and `_<sx>` present iff `t =/= ti`
  - traps on `null`

* `struct.set <typeidx> <fieldidx>` writes field `i` of a structure
  - `struct.set $t i : [(ref null $t) ti] -> []`
    - iff `$t = struct (mut1 t1)^i (var ti) (mut2 t2)*`
    - and `t = unpacked(ti)`
  - traps on `null`


#### Arrays

* `array.new_with_rtt <typeidx>` allocates an array with RTT information determining its [runtime type](#values)
  - `array.new_with_rtt $t : [t' i32 (rtt n $t)] -> [(ref $t)]`
    - iff `$t = array (var t')`
  - allocation failure behavior is [implementation-defined](#failure)

* `array.new_default_with_rtt <typeidx>` allocates an array and initialises its fields with the default value
  - `array.new_default_with_rtt $t : [i32 (rtt n $t)] -> [(ref $t)]`
    - iff `$t = array (var t')`
    - and `t'` is defaultable
  - allocation failure behavior is [implementation-defined](#failure)

* `array.get_<sx>? <typeidx>` reads an element from an array
  - `array.get_<sx>? $t : [(ref null $t) i32] -> [t]`
    - iff `$t = array (mut t')`
    - and `t = unpacked(t')`
    - and `_<sx>` present iff `t =/= t'`
  - traps on `null` or if the dynamic index is out of bounds

* `array.set <typeidx>` writes an element to an array
  - `array.set $t : [(ref null $t) i32 t] -> []`
    - iff `$t = array (var t')`
    - and `t = unpacked(t')`
  - traps on `null` or if the dynamic index is out of bounds

* `array.len <typeidx>` inquires the length of an array
  - `array.len $t : [(ref null $t)] -> [i32]`
    - iff `$t = array (mut t)`
  - traps on `null`


#### Unboxed Scalars

Tentatively, support a type of guaranteed unboxed scalars.

* `i31.new` creates an `i31ref` from a 32 bit value, truncating high bit
  - `i31.new : [i32] -> [i31ref]`

* `i31.get_u` extracts the value, zero-extending
  - `i31.get_u : [i31ref] -> [i32]`

* `i31.get_s` extracts the value, sign-extending
  - `i31.get_s : [i31ref] -> [i32]`

Perhaps also the following short-hands:

* `ref.is_i31` checks whether a reference is an i31
  - `ref.is_i31 : [anyref] -> [i32]`
  - equivalent to `(rtt.canon i31) (ref.test)`

* `ref.as_i31` converts to an integer reference
  - `ref.as_i31 : [anyref] -> [i31ref]`
  - traps if reference is not an integer
  - equivalent to `(rtt.canon i31) (ref.cast)`


#### Runtime Types

* `rtt.canon <heaptype>` returns the RTT of the specified type
  - `rtt.canon t : [] -> [(rtt n t)]`
  - `n = 0` iff `t = any`, and `n = 1` otherwise
  - multiple invocations of this instruction yield the same observable RTTs
  - this is a *constant instruction*
  - equivalent to `(rtt.sub 1 any t (rtt.canon any))`, except when `t` itself is `any`

* `rtt.sub <n> <heaptype1> <heaptype2>` returns an RTT for `heaptype2` as a sub-RTT of a the parent RTT operand for `heaptype1`
  - `rtt.sub n t1 t2 : [(rtt n t1)] -> [(rtt (n+1) t2)]`
    - iff `t2 <: t1`
  - multiple invocations of this instruction with the same operand yield the same observable RTTs
  - this is a *constant instruction*

TODO: Add the ability to generate new (non-canonical) RTT values to implement casting in nominal type hierarchies.


#### Casts

* `ref.test <heaptype1> <heaptype2>` tests whether a reference value's [runtime type](#values) is a [runtime subtype](#runtime) of a given RTT
  - `ref.test t1 t2 : [(ref null t1) (rtt n t2)] -> [i32]`
     - iff `t2 <: t1`
  - returns 1 if the first operand is not null and its runtime type is a sub-RTT of the RTT operand, 0 otherwise

* `ref.cast <heaptype1> <heaptype2>` casts a reference value down to a type given by a RTT representation
  - `ref.cast t1 t2 : [(ref null t1) (rtt n t2)] -> [(ref t2)]`
     - iff `t2 <: t1`
  - traps if the first operand is null or its runtime type is not a sub-RTT of the RTT operand

* `br_on_cast <labelidx> <heaptype1> <heaptype2>` branches if a value can be cast down to a given reference type
  - `br_on_cast $l t1 t2 : [(ref null t1) (rtt n t2)] -> [(ref null t1)]`
    - iff `t2 <: t1`
    - and `$l : [(ref t2)]`
  - branches iff the first operand is not null and its runtime type is a sub-RTT of the RTT operand
  - passes cast operand along with branch


## Binary Format

### Types

This extends the [encodings](https://github.com/WebAssembly/function-references/blob/master/proposals/function-references/Overview.md#types-1) from the typed function references proposal.

#### Storage Types

| Opcode | Type            |
| ------ | --------------- |
| -0x06  | `i8`            |
| -0x07  | `i16`           |

#### Reference Types

| Opcode | Type            | Parameters | Note |
| ------ | --------------- | ---------- | ---- |
| -0x10  | `funcref`       |            | from reftype proposal |
| -0x11  | `externref`     |            | from reftype proposal |
| -0x12  | `anyref`        |            | |
| -0x13  | `eqref`         |            | |
| -0x14  | `(ref null ht)` | `ht : heaptype (s33)` | from funcref proposal |
| -0x15  | `(ref ht)`      | `ht : heaptype (s33)` | from funcref proposal |
| -0x16  | `i31ref`        |            | |
| -0x17  | `(rtt n ht)`    | `n : u32`, `ht : heaptype (s33)` | |

#### Heap Types

The opcode for heap types is encoded as an `s33`.

| Opcode | Type            | Parameters | Note |
| ------ | --------------- | ---------- | ---- |
| i >= 0 | `(type i)`      |            | from funcref proposal |
| -0x10  | `func`          |            | from funcref proposal |
| -0x11  | `extern`        |            | from funcref proposal |
| -0x12  | `any`           |            | |
| -0x13  | `eq`            |            | |
| -0x17  | `i31`           |            | |

#### Defined Types

| Opcode | Type            | Parameters |
| ------ | --------------- | ---------- |
| -0x21  | `struct ft*`    | `ft* : vec(fieldtype)` |
| -0x22  | `array ft`      | `ft : fieldtype`       |

#### Field Types

| Type            | Parameters |
| --------------- | ---------- |
| `field t mut`   | `t : storagetype`, `mut : mutability` |


### Instructions

| Opcode | Type            | Parameters |
| ------ | --------------- | ---------- |
| 0xd5   | `ref.eq`        |            |
| 0xfb01 | `struct.new_with_rtt $t` | `$t : typeidx` |
| 0xfb02 | `struct.new_default_with_rtt $t` | `$t : typeidx` |
| 0xfb03 | `struct.get $t i` | `$t : typeidx`, `i : fieldidx` |
| 0xfb04 | `struct.get_s $t i` | `$t : typeidx`, `i : fieldidx` |
| 0xfb05 | `struct.get_u $t i` | `$t : typeidx`, `i : fieldidx` |
| 0xfb06 | `struct.set $t i` | `$t : typeidx`, `i : fieldidx` |
| 0xfb11 | `array.new_with_rtt $t` | `$t : typeidx` |
| 0xfb12 | `array.new_default_with_rtt $t` | `$t : typeidx` |
| 0xfb13 | `array.get $t` | `$t : typeidx` |
| 0xfb14 | `array.get_s $t` | `$t : typeidx` |
| 0xfb15 | `array.get_u $t` | `$t : typeidx` |
| 0xfb16 | `array.set $t` | `$t : typeidx` |
| 0xfb17 | `array.len $t` | `$t : typeidx` |
| 0xfb20 | `i31.new` |  |
| 0xfb21 | `i31.get_s` |  |
| 0xfb22 | `i31.get_u` |  |
| 0xfb30 | `rtt.canon ht` | `ht : heaptype` |
| 0xfb31 | `rtt.sub n ht1 ht2` | `n : u32`, `ht1 : heaptype`, `ht2 : heaptype` |
| 0xfb40 | `ref.test ht1 ht2` | `ht1 : heaptype`, `ht2 : heaptype` |
| 0xfb41 | `ref.cast ht1 ht2` | `ht1 : heaptype`, `ht2 : heaptype` |
| 0xfb42 | `br_on_cast $l ht1 ht2` | `$l : labelidx`, `ht1 : heaptype`, `ht2 : heaptype` |


## JS API

See [GC JS API document](MVP-JS.md) .


## Questions

* Should RTT presence be made explicit in struct types and ref types?
  - for example, `(struct rtt ...)` and `rttref <: anyref`
  - only these types would be castable

* Provide a way to make data types non-eq, especially immutable ones?
