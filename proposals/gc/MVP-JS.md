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


## Summary

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


## Walkthrough

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


### Value Type Objects

Corresponding to the set of [field types](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
in the WebAssembly GC proposal, the JS Typed Objects proposal includes an
open-ended set of [Value Type Objects](TODO)
which contain `[[Read]]` and `[[Write]]` [internal methods](https://tc39.github.io/ecma262/#sec-object-internal-methods-and-internal-slots)
that convert to and from arbitrary JavaScript values and the pure typed values
that WebAssembly is defined to interact with.

The JS Typed Object proposal includes a [generally-applicable set of Value Type Objects](TODO).
This general set is extended with additional Value Type Objects in the
`WebAssembly` namespace [described below](#other-webassembly-value-types), so
that all WebAssembly field types have a corresponding Value Type Object. The 
generally-applicable Value Type Objects defined by the JS Typed Object proposal
are broken into two categories:

* *Primitive* Value Types, exposed as singleton objects: `uint8`,
  `uint16`, `uint32`, `uint64`, `int8`, `int16`, `int32`, `int64`, `float32`,
  `float64`, `any`, `string`.

* *Compound* Value Types, which are produced via the `ref` property
   on another kind of object...


### Type Definition Objects

Corresponding to the [Type Definitions](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#type-definitions)
in the WebAssembly GC proposal, the JS Typed Objects proposal defines constructors
for [Type Definition Objects](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#type-definitions).
Type Definition Objects are constructed by the [`StructType`](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#struct-type-definitions)
and [`ArrayType`](TODO) constructors which are passed Value Type Objects for
each field/element.

Type Definition Objects serve three purposes:

* When a Type Definition is [exported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#exports)
  by a wasm module, a Type Definition Object is produced in the [exportsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).

* When a Type Definition is [imported](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#imports)
  by a wasm module, a Type Definition Object is expected in the [importsObject](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module).

* A Type Definition Object is actually a constructor function which can be
  called to construct another kind of object...


### Typed Objects

Corresponding to the [structs](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
and [arrays](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
of the WebAssembly GC proposal, the JS Typed Object proposal defines a new kind of Exotic Object
called a [Typed Object](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md#instantiation).
Typed Objects can be both created from JS by calling a Type Definition Object
as a constructor and created wasm from wasm by executing [`struct.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#structures)
and [`array.new`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#arrays)
instructions. A Typed Object's state is exclusively read and written from JS
through the `[[Read]]` and `[[Write]]` internal methods of its fields'/elements'
associated Value Type Objects.

From an implementation perspective, this identification of wasm structs/arrays with
JS Typed Objects should not incur significant overhead: all of a Typed Object's
internal slots/methods (e.g., `[[Prototype]]`) are determined by the Type
Definition Object and thus can be stored in the existing engine-internal
metadata structure (the [Shape, Hidden Class, Map, Type, Structure, ...](https://youtu.be/5nmpokoRaZI?t=725))
that is typically stored as the first word of any GC allocation.

One important question about Typed Objects is how the identity of their
prototype is determined at the point of `struct.new`/`array.new`. While it is
tempting to have a per-Realm table of prototypes, indexed by the structure of
the type definition, this would lead to unintentional and unavoidable collisions
as unrelated packages put helpers and other methods on these shared prototypes.

Instead, there are two cases for determining the prototype of a Typed Object when
it is constructed via `struct.new`/`array.new`:

* If the type definition is *internal* (defined by the WebAssembly module, not
  imported), the prototype is `null`.

* If the dyped definition is *imported*, the instance must be given a
  Type Definition Object at instantiation-time, and this Type Definition
  Object (which is a constructor) determines the prototype with its
  (immutable) `prototype` property.

An important detail of the JS Typed Objects proposal is that the
[own properties](https://tc39.github.io/ecma262/#sec-own-property)
of a Typed Object all have dense-index property names. If user-defined
(non-indexed) property names are supplied when the Type Definition Object is
constructed, they get defined as accessor properties on the `prototype` property
of the Type Definition Object. These accessor properties forward to the
associated indexed own property of the receiver. Combined with the wasm
prototype-selection behavior described above, that means that to give a
WebAssembly-constructed Typed Object property names, JavaScript must first
create a Type Definition Object with the appropriate names, import it from
WebAssembly, and then use that type import to construct structs/arrays.


## Examples

Here, a Typed Definition Object is created in JS and used to create a Typed
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
;; example1.wat --> example1.wasm
(module
   (type $Point (struct (field $x i32) (field $y i32)))
   (func (export "addXY") (param (ref $Point)) (result i32)
       (i32.add
           (struct.get $Point $x (get_local 0))
           (struct.get $Point $y (get_local 0)))
   )
)
```

which allows `pt` to be passed to `addXY`:

```js
WebAssembly.instantiateStreaming(fetch('example1.wasm'))
.then(({instance}) => {
    assert(instance.exports.addXY(pt) == 3);
});
```

Additionally, the internal type definition `$Point` can be exported by adding
the following to `example1.wat` above:

```wat
   (export "wasmPoint" (type $Point))
```

Which produces a distinct Type Definition Object that has no prototype
and thus no property names:

```js
WebAssembly.instantiateStreaming(fetch('example1.wasm'))
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

Moreover repeated instantations of `example1.wasm` will produce distinct Type
Definition Objects for `wasmPoint`.

To see the distinction between internal type defintions and type imports in
action, consider the following WebAssembly module that calls `struct.new`.

```wat
;; example2.wat --> example2.wasm
(module
    (type $PointImport (import "" "Point") (eq (struct (field $x i32) (field $y i32))))
    (func (export "newImport") (result (ref $PointImport))
        (struct.new $PointImport (i32.const 10) (i32.const 10))
    )

    (type $PointInternal (struct (field $x i32) (field $y i32)))
    (func (export "newInternal") (result (ref $PointInternal))
        (struct.new $PointInternal (i32.const 20) (i32.const 20))
    )
)
```

Note that the [`eq` constraint](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#imports)
requires the imported type definition be structurally equivalent to the given
type definition, not merely a subtype of it and `struct.new` is only valid for
type imports with the `eq` constraint.

Viewing these objects from JS shows the difference:

```js
const Point = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);

WebAssembly.instantiateStreaming(fetch('example2.wasm'), {'':{Point}})
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


## The Nominal vs. Structural Problem and Solution

The soundness of the basic approach outlined above is predicated on two
conditions:
* that the dynamic checks performed by [Value Type Objects](#value-type-objects)'
  internal `[[Read]]` and `[[Write]]` methods preserve the invariants assumed by
  WebAssembly's static type system; and
* that WebAssembly's static type system ensures that the runtime
  WebAssembly `struct.set`/`array.set` instructions do not violate
  the JS invariants otherwise dynamically ensured by the Value Type Objects.

One place where WebAssembly and JavaScript invariants don't naturally
line up is *reference types*.

In particular, the JS Typed Object proposal `ref` Value Type Objects are
[defined](TODO)
to preserve the usual "nominal typing" of JavaScript, where a field
type implies a specific prototype *identity*. In contrast, the wasm GC proposal's
[static subtyping relation](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#subtyping)
is *structural*, ensuring only field types and layouts.

To see this problem, consider the following JS code which hands a mutable `Rect`
Typed Object to WebAssembly and then inspects it afterwards.

```js
const Point = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);
const Rect = new StructType([{name: "p1", type: Point.ref}, {name: "p2", type: Point.ref}]);
var r = new Rect(new Point(1,1), new Point(2,2));

wasmInstance.exports.goNuts(r);

assert(r.p1 instanceof Point);
assert(r.p2 instanceof Point);
```

Without knowing anything about `wasmInstance`, can JS assumed, based solely on
the field types of `Rect`, that the asserts hold?

If the JS `ref` Value Types were unified with the WebAssembly
`ref` type constructor, the answer would be "no": `wasmInstance`
could assign any Typed Object with two `i32` fields, including 
those with a `null` `__proto__`, as shown above.

This would be surprising from a JS perspective and also give up potential
WebAssembly Host Binding optimizations that are mentioned later. Thus, as
a starting point, the following WebAssembly module:

```wat
;; example3.wat --> example3.wasm
(module
    (type $P (struct (field i32) (field i32)))
    (type $R (struct (field $x1 (ref $P)) (field $x2 (ref $P))))
    (func (export "goNuts") (param (ref $R))
        (struct.set $R $x1
            (get_local 0)
            (struct.new $P (i32.const 10) (i32.const 20)))
    )
)
```

will throw when passed a `Point` Typed Object because of the attempt to
reinterpret the *nominal* field types of `Rect` with the *structural*
field types of `$R`.

```js
WebAssembly.instantiateStreaming(fetch('example3.wasm'))
.then(({instance}) => {
    instance.exports.goNuts(new Rect(new Point(1,2), new Point(3,4));  // throws
});
```

For the call to succeed, the WebAssembly module must intead *import* the
exact Type Definition Object and use that type import in all relevant
function signatures:

```wat
;; example4.wat --> example4.wasm
(module
    (type $Point (import "" "Point") (eq (struct (field $x i32) (field $y i32))))
    (type $Rect (struct (field (ref $Point)) (field (ref $Point))))
    (func (export "goNuts") (param (ref $Rect))
        (struct.set $R $x1
            (get_local 0)
            (struct.new $Point (i32.const 10) (i32.const 20)))
    )
)
```

With this module, the following JS code can instantiate the module with a Type
Definition Object and then later pass it instances of the same Type Definition
Object (but no other:

```js
const Point = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);

WebAssembly.instantiateStreaming(fetch('example4.wasm'), {'':{Point}})
.then(({instance}) => {
    var rect = new Rect(new Point(1,2), new Point(3,4));
    instance.exports.goNuts(rect);  // succeeds
    assert(rect.x1 instanceof Point);
    assert(rect.x1.x === 10);
    assert(rect.x1.y === 20);

    const Point2 = new StructType([{type: int32}, {type: int32}]);
    instance.exports.goNuts(new Point2(1,2));  // throws
});
```

With this, the nominal invariants natural to JS can be preserved by a
combination of instantiation-time and run-time checks.

But what about the other direction: what if WebAssembly exports a `struct`
type definition that uses a (structural) WebAssembly `ref` type?  What is needed
is a new Value Type Object that enforces the weaker structural subtyping rules
of the wasm static type system.

Since the set of Value Type Objects is open-ended, the WebAssembly JS API adds
a new Value Type constructor function: `WebAssembly.ref(T)`. Using this, JS can
create a suitable Type Definition Object whose instances can be passed to the
above `example3.wasm` because its fields are structurally typed:

```js
const Point2 = new StructType([{name: "x", type: int32}, {name: "y", type: int32}]);
const Point2Ref = WebAssembly.ref(Point2);
const Rect2 = new StructType([{name: "p1", type: PointRef}, {name: "p2", type: PointRef}]);

WebAssembly.instantiateStreaming(fetch('example3.wasm'))
.then(({instance}) => {
    var rect = new Rect2(new Point2(1,2), new Point2(3,4));
    assert("x" in rect.x1);
    instance.exports.goNuts(rect);
    assert(!("x" in rect.x1));
    assert(rect.x1[0] === 10);
    assert(rect.x1[1] === 20);

    // sure, why not:
    rect.x1 = new Point(100,100);
    assert(rect.x1.x === 100);
});
```

The distinction between the two kinds different reference subtype semantics is
unfortunate, but the expectation is that practical uses will generate all these
Type Definition Objects as part of the usual JS boilerplate glue code and
end users would simply interact with objects that were either tuple-y or had property
names as expected from the source language. (For example, a WebAssembly-friendly
Flow variant might use structural typing for [Tuple Types](https://flow.org/en/docs/types/tuples/)
and nominal typing for [Class Types](https://flow.org/en/docs/types/classes/).

Note that, in addition to dynamic checks when JS passes a value to WebAssembly
(either as an argument to a wasm exported function or a return value from a
wasm imported function), the instantiation algorithm must ensure that imported
type definitions' fields' types are compatible.

For example, given the following module with two dependent type imports:

```wat
;; example5.wat --> example5.wasm
(module
    (type $Point (import "" "Point") (eq (struct (field i32) (field i32))))
    (type $Rect (import "" "Rect") (eq (struct (field (ref $Point)) (field (ref $Point)))))
    ;; ...
)
```

this instantiation would succeed:

```js
const Point = new StructType([{type: int32}, {type: int32}]);
const Rect = new StructType([{type: Point.ref}, {type: Point.ref}]);

WebAssembly.instantiateStreaming(fetch('example5.wasm'), {'':{Point, Rect}});
```

while this instantiation would fail because of the `Point1`/`Point2` mismatch in the
field types of `Rect`:

```js
const Point1 = new StructType([{type: int32}, {type: int32}]);
const Point2 = new StructType([{type: int32}, {type: int32}]);
const Rect = new StructType([{type: Point2.ref}, {type: Point2.ref}]);

WebAssembly.instantiateStreaming(fetch('example5.wasm'), {'':{Point1, Rect}});
```

This instantiation-time checking would extend to the signatures of imported
typed functions as an extension of the existing wasm-to-wasm import type checking
performed by [instantiate_module](https://webassembly.github.io/spec/core/appendix/embedding.html#embed-instantiate-module).

Additionally, using type imports of [Web IDL interface objects](https://heycam.github.io/webidl/#interface-object),
the signatures of [Web IDL methods](https://heycam.github.io/webidl/#idl-operations) could
be checked at instantiation-time, eliminating the normal dynamic type checks
performed by JavaScript at call-time. In this way, the preservation of nominal
typing via type imports can yield performance benefits, not just error-catching
benefits.


## Other WebAssembly Value Types

In addition to `WebAssembly.ref(T)`, these additional Value Type Object singletons
and constructor functions would be added to the `WebAssembly` namespace to
reflect all the other field types in the GC proposal:
* `WebAssembly.eqref` : singleton reflecting [`eqref`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#value-types)
* `WebAssembly.optref(T)` : constructor function reflecting [`optref <typeidx>`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#value-types),
  given any Type Definition Object
* `WebAssembly.i31ref` : singleton reflecting [`i31ref`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#value-types)
* `WebAssembly.rtt(T)` : constructor function reflecting [`rtt <typeidx>`](https://github.com/WebAssembly/gc/blob/master/proposals/gc/MVP.md#value-types),
  given any Type Definition Object
* `WebAssembly.funcref(T)` : constructor function reflecting [`funcref <functype>`](https://github.com/WebAssembly/reference-types/blob/master/proposals/reference-types/Overview.md#typed-function-references),
  assuming the eventual addition of a `FuncType` Type Definition constructor.

Additional Value Type singletons and constructor functions could be added in the
future as WebAssembly's GC types evolve.

## Summary of JS API Additions

Assuming the [Typed Objects proposal](https://github.com/tschneidereit/proposal-typed-objects/blob/master/explainer.md)
can be standardized in TC39 for inclusion in ES262 as a builtin part of the
JavaScript language, the WebAssembly JS API can build on Typed Objects the way
it currently builds on Number and ([soon](https://github.com/WebAssembly/JS-BigInt-integration))
BigInt.

With that, the remaining additions to the [WebAssembly JS API](https://webassembly.github.io/spec/js-api/index.html) are:
* New [Value Type singletons and constructor functions](#other-webassembly-value-types).
* New checks in the [instantiation algorithm](https://webassembly.github.io/spec/js-api/index.html#instantiate-a-webassembly-module)
  to ensure type imports are used consistently, preserving
  [JS nominal typing](#the-nominal-vs-structural-problem-and-solution).
* New cases in [ToWebAssemblyValue](https://webassembly.github.io/spec/js-api/index.html#towebassemblyvalue)
  to allow Type Objects to be supplied for struct/array reference types when the
  Type Object's type is a subtype of the target WebAssembly type
  (respecting [JS nominal typing](#the-nominal-vs-structural-problem-and-solution))
  subtype of the destination WebAssembly type.
* New cases in [ToJSValue](https://webassembly.github.io/spec/js-api/index.html#tojsvalue)
  that trivially return GC reference types as the Typed Object they already are.
