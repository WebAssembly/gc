# Requirements for GC

This document identifies the key requirements for the managed memory proposal. Below we refer to the version of WASM with managed memory as being WASM-GC.

## Goals

1. Support for host-provided GC

   Allow language implementers to use host-provided GC features as their primary means of supporting memory management. 
   
   On the whole, it would be preferable if language implementers could target WASM-GC as a natural target for their language. While it is difficult to be precise about this, an ideal scenario would be that language implementers could target WASM-GC as though it were just another back-end. In particular, targeting WASM-GC should try to avoid requiring changes to earlier stages of a compiler - such as the type checker or source-level transformations.
   
### Non-Goals
1. Support for linear memory GC.

   We do not attempt with this proposal to support alternate memory management strategies that rely on collecting linear memory.
   
## Criteria

A criterion is intended to act as a metric of a 'soft value', such as 'desireability' or 'implementability'. Criteria are especially important when weighing the relative merits of features and in determining the importance that some scenario is satisfied.

1. Prioriterize popular languages.
   When deciding which features to provide it is important to place emphasis on features that are more likely to be used. We prioriterize support for the popular programming languages; while it is difficult to be precise about this, one measure is a public index such as the TIOBE index. The TIOBE ranking of the top 12 languages with managed memory (from the top 20 languages) is Java, Python, C#, Visual Basic, PHP, SQL, Swift, Go, Ruby, MATLAB, Perl, Scratch.
   
   Within these languages, there are languages which are (largely) statically typed -- such as Java and C# -- and languages that are dynamically typed -- such as Python. We prioriterize statically typed languages over dynamically typed language; because those languages are often more performance sensitive, and because support for statically typed languages can often be used for dynamically typed languages.
   
1. Security is more important than architectural integrity.

1. Architectural integrity is more important than performance.
   'Architectural Integrity' is intended to denote simplicity/coherence of design. Generally speaking, architectural integrity can be measured in terms of the number of concepts and the complexity of their relationships.
   
   The more complex an architecture is, the harder it will be to extend or to modify; this, in turn, inhibits our ability to extend WASM-GC with new features.
   
   We prioriterize simple, composeable architectures over solution-oriented architectures. This will help to ensure that WASM-GC can evolove and be part of future WASM evolution.
   
   Our reasoning here is that performance is often the result of progressive tuning of an implementation. It can typically be improved over time. On the other hand, architectural deficiencies are very difficult to correct.
      
1. Performance is more important than convenience.

   Since WASM-GC is not intended as a user-facing technology, convenience here refers to the ease with which toolchain authors can target WASM-GC. 
   
   Convenience for toolchain authors is still important however, as that affects adoption of WASM-GC. 

   
## Critical Success Factors

A critical success factor is an aspect or property of possible solutions that may or may not be directly focused on the primary objective, but none-the-less is estimated to be crucially important to the success of the effort.

1. Permit ‘cycle detection’ between host structures and language structures; so that such cycles can be collected if there are no other references to them.

   When a WASM-GC module accesses host capabilities, or when a host application access structures from a WASM-GC library, cross references between them are likely to be established. For example, a DOM node may have an event listener that is actually implemented in WASM. The event listener, in turn, may have a reference to the DOM node it is listening to. This represents a cycle between the host and WASM-GC. If there are no other references to this cycles (if, for example, the DOM node is removed) then the entire cycle must be able to be collected.

1. Performance implications of WASM-GC code should be straightforward.

   A general principle behind WASM itself is that performance should not require special implementation techniques on the part of the engine. I.e., it should not be required that the engine discover particular opportunities for improving performance. In particular, it is the responsibility of languages implementers to generate WASM-GC code that embodies performant strategies.
   
   For example, if a type cast is potentially eliminatable, then the engine should not be required to discover that fact; rather the toolchain should be able to eliminate the type cast.
   
1. Support code migration.

   This refers to a potential code migration strategy; where an application starts as a JavaScript code base (say), and is then progressively migrated to another language (hosted on WASM-GC). During this migration process, individual functions and modules may be ported from JavaScript whilst the remaining codebase remains in JavaScript. 
   Interoperability between WASM-GC code and JavaScript is critical for the success of this strategy; in particular, structures defined in one language may need to be accessed by another.
   Code Migration itself is a CSF because it underlies a realistic assumption about porting libraries and applications to WASM-GC.

## Requirements

1. Support for typical memory layouts employed by languages like Java/C#/Kotlin.

1. Support for V-tables for object layout.

1. Support for embedded arrays.

   Many languages use a combined structure consisting of a fixed set of fields together with an array. This is, for example, how arrays themselves are realized in languages like Java.
   
   Potentially restricted to a single embedded array.
   
1. Support for parametric polymorphic types.
   Specifically, support for languages that support parametric type polymorphism; and subtype polymorphism. 
   The primary task of the WASM type system is to be able to reliably and securely identify the representations of values. As such, it is not clear that WASM's type system needs to be polymorphic. However, many statically typed languages are polymorphic, and there are multiple strategies for realizing them -- from a so-called uniform representation (for representing parametric types) to compile-time monomorphization.
   

### Non-Requirements
1. Arbitrary interoperability between different languages on the wasm.
   While it may be tempting to try to support arbitrary interoperability across languages -- by enabling cross language access to data structures in the case of WASM-GC -- this is fraught with many difficulties; not the least of which are caused by those languages themselves.
   The task of WASM-GC is to enable managed languages to represent their structures in such a way as can be managed by the host. This does not imply interoperability between languages or between languages and the host.
1. Arbitrary interoperability with host.
   Similar to the above issue.
1. Permit access to host data structures from wasm, and vice versa.
   While it may be desireable to support access to host structures from wasm, and access to wasm structures from the host, it is not the goal of WASM-GC to support this.

## Phased Release
It is unlikely that WASM-GC will be released as a single version. A more approachable strategy involves releasing subsets of the final proposal over time. 

The driver for a given release is the set of applications and capabilities that are unlocked by a given feature set; and their importance.

Without determining a specific road map here, we establish criteria for individual phases of the road map:

1. Each phase should be additive to prior phases.
1. Each phase should identify which scenarios are unlocked by the new features.


