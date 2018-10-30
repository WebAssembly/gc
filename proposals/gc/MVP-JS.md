# GC v1 JS API

This document describes the proposed changes to the
[WebAssembly JS API spec](http://webassembly.github.io/spec/js-api/) that are
associated with the [changes to the WebAssembly core spec](MVP.md).


## Problem

With the [Reference Types proposal](https://github.com/WebAssembly/reference-types/blob/master/proposals/reference-types/Overview.md),
the only reference type values flowing from WebAssembly to JS are:
* `anyref` values containing JS values, which can be returned unmodified
* `ref.null`, which maps to JS `null` ([or `undefined`](https://github.com/WebAssembly/reference-types/issues/9))

With the [GC proposal](Overview.md), which extends the Reference Types proposal,
the fundamental questions for the JS API are:
* How do struct/array references created by [`struct.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
  and [`array.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
  get [converted to JS values](https://webassembly.github.io/spec/js-api/index.html#tojsvalue)?
* Which JS values can be [converted into WebAssembly values](https://webassembly.github.io/spec/js-api/index.html#towebassemblyvalue)
  of struct/array reference type.


## Opportunity

Since normal JavaScript objects have a dynamic shape, making them incompatible
with the GC proposal's structs and arrays, it may be tempting to simply
treat WebAssembly GC things as separate from JavaScript GC things and, e.g.,
only allow opaque references to go back and forth (i.e., `anyref` in both
directions).

Instead, we propose a design that improves the performance of JavaScript both in
isolation and when interoperating with WebAssembly. Specifically, this proposal
defines WebAssembly structs/arrays to simply **be** certain special JavaScript
objects in specification *and* presumed implementation. This design both avoids
costly wrapper-based JS/WebAssembly interoperability schemes and also gives
JavaScript a new kind of high-performance object that should be independently
valuable for optimizing pure JavaScript applications.

The challenge of course is to do this in a way that doesn't inject JS
peculiarities into the core design of GC in WebAssembly or impact the efficiency
of WebAssembly GC (even in JavaScript Host Embeddings).


## Basic Approach

The JavaScript spec allows [Exotic Objects](https://tc39.github.io/ecma262/#sec-exotic-object)
to diverge from Ordinary Object behavior by overriding
[spec-internal methods and slots](https://tc39.github.io/ecma262/#sec-built-in-exotic-object-internal-methods-and-slots).
An example of this is Typed Arrays, which override various
[internal property-access methods](https://tc39.github.io/ecma262/#sec-integer-indexed-exotic-objects)
to turn normal JS property accesses into pure byte-array operations.
This presently allows JavaScript and WebAssembly to both have high-performance
access to WebAssembly's [linear memory](TODO), without injecting JS
peculiarities into the design of linear memory. We propose to do likewise for
WebAssembly structs and arrays.

To do this, we propose to revive, refurbish and repurpose the
[old Typed Objects proposal](http://smallcultfollowing.com/babysteps/pubs/2014.04.01-TypedObjects.pdf).
The [new Typed Objects proposal](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md)
is designed with WebAssembly in mind and is motivated as follows:


### Value Type objects

Corresponding to the set of [field types](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
in the WebAssembly GC proposal, the JS Typed Objects proposal includes an
open-ended set of [Value Type](TODO)
objects which contain `[[Read]]` and `[[Write]]` [internal methods](https://tc39.github.io/ecma262/#sec-object-internal-methods-and-internal-slots)
that convert to and from arbitrary JavaScript values and the pure typed values
that WebAssembly is defined to interact with.

The JS Typed Object proposal includes a [generally-applicable set of Value Type objects](TODO).
This general set is extended by Value Type objects in the [`WebAssembly` namespace](TODO)
below, so that all WebAssembly field types have a corresponding JS Value Type.
The Value Type objects defined by the JS Typed Object proposal are broken into two
categories:

* *Primitive* Value Types, exposed as singleton objects: `uint8`,
  `uint16`, `uint32`, `uint64`, `int8`, `int16`, `int32`, `int64`, `float32`,
  `float64`, `any`, `string`.

* *Compound* Value Types, which are extracted via the `ref` property
   on another kind of object...


### Type Definition objects

Corresponding to the [Type Definitions](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
in the WebAssembly GC proposal, the JS Typed Objects proposal allows the
construction of [Type Definition](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#type-definitions)
objects which describe the fields/elements of a struct/array via
[Value Type](#value-type-objects) objects supplied as arguments to the
[`StructType`](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#struct-type-definitions)
and [`ArrayType`](TODO) constructors.

Type Definition objects serve three purposes:

* When a Type Definition is [exported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#exports),
  a Type Definition object is produced in the [exportsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).

* When a Type Definition is [imported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#imports),
  a Type Definition object is expected in the [importsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).
  This Type Definition object can have either been exported by an
  existing `WebAssembly.Instance` or constructed in JavaScript.

* A Type Definition object is actually a constructor function which can be
  called to construct another kind of object...


### Typed Objects

Corresponding to the [structs](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
and [arrays](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
of the WebAssembly GC proposal, the JS Typed Object proposal defines a new kind of Exotic Objects
called [Typed Objects](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#instantiation).
Whereas structs/arrays are created in WebAssembly by the `struct.new` and
`array.new` instructions, Typed Objects are created in JS by calling a
[Type Definition](#type-definition-objects) constructor.

A Typed Object's state is exclusively read and written through the `[[Read]]`
and `[[Write]]` methods of its fields' Value Type objects. To avoid treating
WebAssembly structs/arrays and Typed Objects as separate entities, with Typed
Objects being created as "wrappers" at the boundary, WebAssembly's
`struct.new`/`array.new` instructions are redefined to actually allocate a whole
Typed Object so that every struct/array reference in a JS embedding of
WebAssembly actually refers to a Typed Object.

From an implementation perspective, this should not incur overhead: all of a
Typed Object's internal slots/methods (e.g., `[[Prototype]]`) are determined by
the Type Definition object and thus can be stored in the existing engine-internal
metadata structure (the [Shape, Hidden Class, Map, Type, Structure, ...](https://youtu.be/5nmpokoRaZI?t=725))
that is already stored as the first word of every engine GC allocation.

One important question about Typed Objects is how the identity of their
prototype is determined at the point of `struct.new`. While it is tempting to
have a per-Realm table of prototypes, looked up by the stucture of the Typed
Object, this would likely lead to unintentional and unavoidable collisions as
unrelated packages put helpers and other methods on these prototypes.

Instead, there are two cases for determining the prototype of a Typed Object when
it is constructed via `struct.new`/`array.new`:

* If the Type Definition is local (defined by the WebAssembly module, not
  imported), the prototype is `null`.

* If the Typed Object is imported, the type import must be fulfilled with a
  Type Definition object at instantiation-time, and this Type Definition
  constructor then determines the prototype. (Type Definition constructors'
  `.prototype` fields are defined to be immutable, so this allows
  instantiation-time determination of the metadata to use at allocation sites.)

An important detail of the JS Typed Objects proposal is that the
[own properties](https://tc39.github.io/ecma262/#sec-own-property)
of a Typed Object all have dense-index property names. If user-defined
non-indexed property names are supplied to the Type Definition object, they get
defined as accessor properties *on the prototype* that forward to the associated
indexed own property of the receiver.

Combining this fact and the prototype-selection behavior above, this means that
to give a WebAssembly-constructed Typed Object property names, JavaScript must
create a Type Definition object with the appropriate names, import it from
WebAssembly, and use that type import to construct structs/arrays. Otherwise,
Typed Objects created from a local Type Definition will appear as
integer-indexed tuples.


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
* What about RTT values?
