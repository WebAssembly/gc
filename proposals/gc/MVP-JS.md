# GC v1 JS API

This document describes the proposed changes to the
[WebAssembly JS API spec](http://webassembly.github.io/spec/js-api/) that are
associated with the [changes to the WebAssembly core spec](MVP.md).


## Problem Statement

With the [Reference Types proposal](https://github.com/WebAssembly/reference-types/blob/master/proposals/reference-types/Overview.md),
any JS value can be converted to an `anyref` value and back, preserving the
exact JS value. The only way to create an `anyref` value in wasm is `ref.null`
which can be trivially converted to a JS `null` ([or `undefined`](https://github.com/WebAssembly/reference-types/issues/9))
value at the JS/wasm boundary.

With the [GC proposal](Overview.md), which extends the Reference Types proposal,
the WebAssembly JS API must now specify:
* How do struct/array references created by [`struct.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
  and [`array.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
  get [converted to JS values](https://webassembly.github.io/spec/js-api/index.html#tojsvalue)?
* Which JS values can be [converted into WebAssembly values](https://webassembly.github.io/spec/js-api/index.html#towebassemblyvalue)
  of struct/array reference type?


## Opportunity

Since normal JavaScript objects have a dynamic shape, making them incompatible
with the wasm GC proposal's structs and arrays, it may be tempting to simply
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
access to WebAssembly's [linear memory](https://webassembly.github.io/spec/core/intro/overview.html#memory), without injecting JS
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

Here, a Typed Definition object is created in JS and used to create a Typed
Object:

```js
const Point = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);
var pt = new Point(1, 2);
assert(pt[0] === 1);
assert(pt[1] === 2);
assert(pt.x === pt[0]);
assert(pt.y === pt[1]);
```

Because names are supplied, `x` and `y` accessors are created on the prototype
allowing named access in addition to indexed tuple access.

Next, a WebAssembly module is defined with a `Point`-compatible struct type
definition, used in the signature of an export:

```wat
;; example.wat --> example.wasm
(module
   (type $Point (struct (field $x i32) (field $y i32)))
   (func (export "addXY") (param (ref $Point)) (result i32)
       (i32.add
           (struct.get $Point $x (get_local 0))
           (struct.get $Point $y (get_local 0))))
)
```

which allows `pt` to be passed to `addXY`:

```js
WebAssembly.instantiateStreaming(fetch('example.wasm'))
.then(({instance}) => {
    assert(instance.exports.addXY(pt) == 3);
});
```

Additionally, the internal type definition `$Point` can be exported by adding
the following to `example.wat` above:

```wat
   (export "wasmPoint" (type $Point))
```

Which produces a distinct Type Definition object that has no prototype
and thus no property names:

```js
WebAssembly.instantiateStreaming(fetch('example.wasm'))
.then(({instance}) => {
    const wasmPoint = instance.exports.wasmPoint;
    assert(Point !== wasmPoint);
    var pt2 = new wasmPoint(3, 4);
    assert(pt2[0], 3);
    assert(pt2[1], 4);
    assert(pt2.__proto__ === null);
    assert(!('x' in pt2));
    assert(instance.exports.addXY(pt) == 3);
    assert(instance.exports.addXY(pt2) == 7);
});
```

Moreover repeated instantations of `example.wasm` will produce distinct Type
Definition objects for `wasmPoint`.

To see the distinction between local type defintions and type imports in
action, consider the following WebAssembly module that calls `struct.new`.

```wat
;; example2.wat --> example2.wasm
(module
    (type $PointImport (import "" "Point") (eq (struct (field $x i32) (field $y i32))))
    (func (export "newImport") (result (ref $PointImport))
        (struct.new $PointImport (i32.const 10) (i32.const 10)))

    (type $PointInternal (struct (field $x i32) (field $y i32)))
    (func (export "newInternal") (result (ref $PointInternal))
        (struct.new $PointInternal (i32.const 20) (i32.const 20)))
)
```

Note that the [`eq` constraint](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#imports)
requires the imported type definition be structurally equivalent to the given
type definition, not merely a subtype of it and `struct.new` is only valid for
type imports with the `eq` constraint.

Viewing these objects from JS shows the difference:

```js
const Point = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);

WebAssembly.instantiateStreaming(fetch('example.wasm'), {'':{Point}})
.then(({instance}) => {
    let p1 = instance.exports.newImport();
    assert(p1.__proto__ === Point.prototype);
    assert(p1.x === 10);
    assert(p1.y === 10);
    let p2 = instance.exports.newInternal();
    assert(p2.__proto__ === null);
    assert(p2[0] === 20);
    assert(p2[1] === 20);
});
```

Note that the declared `(result)` type of `newImport` could have been
`(ref $PointInternal)` or even `anyref`, both of which are supertypes of
`(ref $PointImport)` and neither would change the JS-observable `__proto__`;
all that matters is the type definition specified at `struct.new`.

These examples don't show `ref`. Before we can use `ref`, another fundamental
issue must be explained.


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
