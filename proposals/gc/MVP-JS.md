# GC v1 JS API

This document describes the proposed additions to the
[WebAssembly JS API](http://webassembly.github.io/spec/js-api/) that complement
the core WebAssembly [GC MVP proposal](MVP.md) (henceforth "GC-MVP").


## Problem

With the [Reference Types proposal](https://github.com/WebAssembly/reference-types/blob/master/proposals/reference-types/Overview.md),
the only reference type values flowing from WebAssembly to JS are:
* JS values, that can be returned unmodified
* `ref.null`, which maps to JS `null` ([or `undefined`](https://github.com/WebAssembly/reference-types/issues/9))

With the [GC proposal](Overview.md), the fundamental questions for the JS API are: how
do struct/array references created by [`struct.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
or [`array.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
get [converted to JS values](https://webassembly.github.io/spec/js-api/index.html#tojsvalue) and,
conversely, which JS values can be [converted](https://webassembly.github.io/spec/js-api/index.html#towebassemblyvalue)
into WebAssembly values of struct/array reference type.


## Opportunity

Normal JavaScript objects are extremely dynamic and incompatible with
WebAssembly GC's structs and arrays and so it may be tempting to simply
treat WebAssembly GC as (mostly or fully) separate from JavaScript GC
and, e.g., only allow opaque references to go back and forth (i.e., `anyref`
in both directions).

However, such solutions miss an opportunity to do something that would benefit
JavaScript and WebAssembly performance and interoperability. Thus, the current
proposal defines WebAssembly structs/arrays to simply **be**
([Exotic](https://tc39.github.io/ecma262/#sec-exotic-object)) JavaScript objects
in specification *and* presumed implementation. Such a design would both avoid
costly wrapper-based interop schemes and also give JavaScript a new kind of
ultra-optimizable object that could be independently-valuable to optimize pure
JavaScript applications.

The challenge of course is to do this in a way that doesn't inject JS
peculiarities into the core design of GC in WebAssembly or significantly
impact the efficiency of WebAssembly GC in JavaScript Host Embeddings.


## Basic Approach

The JavaScript spec allows Exotic Objects to diverge from Ordinary
Object behavior by overriding [spec-internal methods and slots](https://tc39.github.io/ecma262/#sec-built-in-exotic-object-internal-methods-and-slots).
An example of this is Typed Arrays, which override various
[property methods](https://tc39.github.io/ecma262/#sec-integer-indexed-exotic-objects)
to turn normal JS property accesses into byte-level accesses of the
abstract array of bytes owned by an `ArrayBuffer`

To expose WebAssembly structs/arrays, we propose to revive, refurbish and
repurpose the [old](http://smallcultfollowing.com/babysteps/pubs/2014.04.01-TypedObjects.pdf)
Typed Objects proposal. The [new proposal](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md)
is designed with WebAssembly in mind and is motivated as follows:


### Value Type Objects

Corresponding to the set of [field types](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
in the GC-MVP, the Typed Object API includes an open-ended set of
[Value Type Objects](TODO),
each of which contain `[[Read]]` and `[[Write]]` [internal methods](https://tc39.github.io/ecma262/#sec-object-internal-methods-and-internal-slots)
which convert between arbitrary JavaScript values and the abstract typed values
that WebAssembly instructions like [`struct.get`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
access directly.

The Typed Object API includes a generally-applicable set of Value Type objects
(whose precise correspondence to WebAssembly GC-MVP field types is explained
below):

* *Primitive* Value Type Objects, exposed as global constants: `uint8`,
  `uint16`, `uint32`, `uint64`, `int8`, `int16`, `int32`, `int64`, `float32`,
  `float64`, `any`, `string`.

* *Compound* Value Type Objects, which are extracted via the `ref` property
   on another kind of object...


### Type Definition Objects

Corresponding to the [Type Definitions](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
of the GC-MVP, the Typed Object API allows the construction of
[Type Definition Objects](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#type-definitions)
which describe the fields/elements of a struct/array via
[Value Type Objects](#value-type-objects) supplied as arguments to the
[`StructType`](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#struct-type-definitions)
or [`ArrayType`](TODO) constructors.

Type Definition Objects serve three purposes:

* When a Type Definition is [exported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#exports),
  a Type Definition Object is produced in [exportsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).

* When a Type Definition is [imported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#imports),
  a Type Definition Object is expected in the [importsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).
  This Type Definition Object can have either been exported by an
  existing `WebAssembly.Instance` or constructed in JavaScript via
  the `StructType` or `ArrayType` constructors.

* A Type Definition Object is itself a constructor function which can be called
  to construct another kind of object...


### Typed Objects

Corresponding to the [structs](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
and [arrays](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
of the GC-MVP, the Typed Object API defines a new kind of Exotic Object
called [Typed Objects](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#instantiation).
Whereas GC-MVP structs/arrays are created in WebAssembly by the `struct.new` and
`array.new` instructions, Typed Objects are created in JS by calling a
[Type Definition Object](#type-definition-objects) as a constructor.

A Typed Object's instance state is entirely contained in its `[[Value]]`
[internal slot](https://tc39.github.io/ecma262/#sec-object-internal-methods-and-internal-slots)
and exclusively read and written through `[[Read]]` and `[[Write]]` methods
of the accessed field's Value Type Object. To avoid treating the WebAssembly
struct/array and the Typed Object as separate entities, with Typed Objects being
allocated as "wrappers" at the boundary, WebAssembly's `struct.new`/`array.new`
instructions are instead defined to allocate a full Typed Object so that every
struct/array reference in (a JS embedding of) WebAssembly actually points to
a Typed Object.

From an implementation perspective, this should not incur overhead: all of a
Typed Object's other internal slots (e.g., `[[Prototype]]`) derive from the Type
Definition Object and so can be stored in the existing engine-internal metadata
structure (the [Shape, Hidden Class, Map, Type, Structure, ...](https://youtu.be/5nmpokoRaZI?t=725))
that is already stored as the first word of every GC allocation

One very important question about Typed Objects is how the identity of their
prototype is determined. While it is tempting to have a per-Realm table of
prototypes, looked up by the stucture of the typed object, this prevents using
Typed Objects like ES classes and will likely lead to accidental name collisions,
e.g., when two unrelated packages are combined into one application that happen
to use the same Struct Type Definitions.

Instead, there are two cases for determining the prototype of a Typed Object when
it is constructed via `struct.new`/`array.new`:

* If the Type Definition is local, the prototype is `null`.

* If the Typed Object is imported, the type import must be instantiated with a
  Type Definition Object, which is a constructor function with an immutable
  `prototype` field, and so that `prototype` field's value is used.

An important detail of the Typed Objects API proposal is that the
only [own properties](https://tc39.github.io/ecma262/#sec-own-property)
of a Typed Object are the indices of its fields. The property names, if they
are supplied, exist as accessor properties on the prototype that simply access
the associated indexed own property.

Combining this fact and the prototype-selection behavior above, this means that
to give a WebAssembly-constructed Typed Object property names visible to JS,
JavaScript must create a Type Definition Object with the appropriate names,
import it from WebAssembly, and use the type import as the type-index
immediate of `struct.new`. Otherwise, Typed Objects created by `struct.new`
of a local Type Definition will appear as an integer-indexed tuple which.


## Examples


TODO: show examples that don't use `ref`.

These examples don't use `ref`; to do that, another fundamental issue must be
explained.


## The Nominal vs. Structural Problem and Solution:

This whole strategy is based on the assumption that the dynamic checks
enforced by the [Value Type Objects](#value-type-objects) correspond
to the invariants ensured by static WebAssembly type system.

One seeming problem is the discrepancy between the 
[dynamic `[[Write]]` checks performed `ref` Value Types](TODO),
which check the *nominal* type of the source value, and the
[static subtyping relation](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#subtyping)
which checks the *structural* type of source value.

To see this problem in action, consider the following examples:

TODO: show JS and wasm separately

* The dynamic coercions applied by the `T.ref` value type object basically
  do a recursive brand check. This check ensures prototype and thus instanceof,
  property names.  This is what you'd expect if you saw (... code) written in
  TypeScript/Flow/etc.  It's a *nominal* type check.
* Meanwhile, when wasm writes `ref`, the checks (LINK) in the GC type system
  only ensure that ... which means this is a *structural* type check.
  So if you see ... in wasm, you cannot assume anything about prototype and thus
  property names.  This is what you'd expect if you saw (... code) in Flow.
* Both make sense for JS/wasm use cases:
  * structural typing is good for low-level composability/ABIs: noone has to
    "own" the type. (E.g., consider how one can simply use `i32` in a sig.)
  * nominal tyyping is simply what JS expects by default (above examples),
    is a useful invariant for JS JIT optimization and reasoning about JS
    programs.
* What gives?  Fortunately, we can express both nominal and structural typing
  in both wasm and JS:
  * JS:
    * Nominal: `T.ref`
    * Structural: a new value type object: `WebAssembly.structRef(T)`
  * WebAssembly:
    * Structural: `ref`
    * Nominal: a suitable type import
* The big question is how the last one works: ...


## Other WebAssembly Value Types Objects

TODO: optref, eqref, i31ref, ...


## So what is the actual JS API proposal?
TODO
* Build on top of the Typed Object (link) proposal (which goes in the JS spec)
* Add to the `WebAssembly` namespace:
  * New value type objects: `structRef`, `optRef`, ...
* Instantiation changes:
  * Described above
* ToWebAssemblyValue() changes:
* ToJSValue() changes:
* TODO: other things?


## TODO
* RTT values (which may get removed anyway...)
