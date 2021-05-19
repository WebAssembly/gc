# Requirements for GC

This document identifies the key requirements for the managed memory proposal. Below we refer to the version of Wasm with managed memory as being Wasm-GC.

## Goals

1. Support for host-provided GC

   Allow language implementers to use host-provided GC features as their primary means of supporting memory management. 
   
   On the whole, it would be preferable if language implementers could use Wasm-GC as a natural target for their language. While it is difficult to be precise about this, an ideal scenario would be that language implementers could target Wasm-GC as though it were just another back-end. In particular, targeting Wasm-GC should try to avoid requiring changes to earlier stages of a compiler - such as the type checker or source-level transformations.
   
### Non-Goals
1. Support for linear memory GC.

   The focus of this effort is in host-provided GC support. There may be additional efforts aimed at improving the capabilities of Wasm to support so-called linear memory GC; but these are outside the scope of this work. 
   
## Criteria

A criterion is intended to act as a metric of a 'soft value', such as 'desireability' or 'implementability'. Criteria are especially important when weighing the relative merits of features and in determining the importance that some scenario is satisfied.

1. Prioritize features used by popular languages.
   
   When deciding which features to provide it is important to place emphasis on features that are more likely to be used. We prioritize support for the languages that are most likely to drive adoption of Wasm-GC; this is likely to be the result of a combination of usage of the language and its likelyhood to be used in a Wasm-GC engine.
   
   The 2020 StackOverflow survey reported that the [most popular managed memory languages](https://insights.stackoverflow.com/survey/2020#technology-most-loved-dreaded-and-wanted-languages-loved) -- from the top 20 -- were Typescript, Python, Kotlin, Go, Julia, Dart, C#, Swift, JavaScript, SQL, Shell, HTML/CSS, Scala, Haskell, R, Java, Ruby, PHP. 

   Within these languages, there are languages which are (largely) statically typed -- such as Java and C# -- and languages that are dynamically typed -- such as Python. We prioritize statically typed languages over dynamically typed language; because those languages are often more performance sensitive, and because support for statically typed languages can often be used for dynamically typed languages.
   
1. Security is more important than architectural integrity.

1. Architectural integrity is more important than performance.
   'Architectural Integrity' is intended to denote simplicity/coherence of design. Generally speaking, architectural integrity can be measured in terms of the number of concepts and the complexity of their relationships.
      
   We prioritize simple, composeable architectures over solution-oriented architectures. This will help to ensure that Wasm-GC can evolve and be part of future Wasm evolution.
   
   Our reasoning here is that performance is often the result of progressive tuning of an implementation. It can typically be improved over time. On the other hand, architectural deficiencies are very difficult to correct.
      
1. Performance is more important than convenience.

   Since Wasm-GC is not intended as a user-facing technology, convenience here refers to the ease with which toolchain authors can target Wasm-GC. 
   
   Convenience for toolchain authors is still important however, as that affects adoption of Wasm-GC. 

   
## Critical Success Factors

A critical success factor is an aspect or property of possible solutions that may or may not be directly focused on the primary objective, but none-the-less is estimated to be crucially important to the success of the effort.

1. Permit ‘collection of unreachable cycles’ between host structures and language structures; so that such cycles can be collected if there are no other references to them.

   When a Wasm-GC module accesses host capabilities, or when a host application access structures from a Wasm-GC library, cross references between them are likely to be established. For example, a DOM node may have an event listener that is actually implemented in Wasm. The event listener, in turn, may have a reference to the DOM node it is listening to. This represents a cycle between the host and Wasm-GC. If there are no other references to this cycles (if, for example, the DOM node is removed) then the entire cycle must be able to be collected.

1. Performance implications of Wasm-GC code should be straightforward.

   A general principle behind Wasm itself is that performance should not require special implementation techniques on the part of the engine.
   For example, if a type cast is potentially eliminatable, then the engine should not be required to discover that fact; rather the toolchain should be able to eliminate the type cast.
   
1. Support sharing of entities.

   There is significant potential for interoperability between Wasm-hosted languages and Host-based languages (of which JavaScript is the most important example).
   
   Given the inherent problems of supporting arbitary interoperability between languages; it is difficult to give a precise criterion for this. However, being able to share entities between different languages supported on Wasm, and between Wasm and JavaScript, is important to the success of Wasm. We can summarize this in terms of capability requirements and performance requirements:
   
   1. An entity that originates in JavaScript should be accessible by Wasm; in particular, changes to the state of the entity from JavaScript/Wasm should be directly visible to each other.
      1. An important potential limitation here is that it may not be *all* changes to the state; but certain publicly visible changes.
   1. Access to elements of the state of the shared entity (again, mutually agreed elements), should not be unduly disadvantaged.
   
   Note that we focus here on sharing of data. Sharing of functions is already accounted for in the design of Wasm and in the JavaScript API for Wasm.
 
1. Support code migration.

   This refers to a potential code migration strategy; where an application starts as a JavaScript code base (say), and is then progressively migrated to another language (hosted on Wasm-GC). During this migration process, individual functions and modules may be ported from JavaScript whilst the remaining codebase remains in JavaScript. Interoperability between Wasm-GC code and JavaScript is critical for the success of this strategy; in particular, structures defined in one language may need to be accessed by another. Code Migration itself is a CSF because it underlies a realistic assumption about porting libraries and applications to Wasm-GC.

## Requirements

1. Support for typical memory layouts employed by languages like Java/C#/Kotlin.

1. Support for method-tables for object layout (or, more abstractly, being able to ensure that methods can be associated with objects in a way that reflects the semantics of the languages being supported).

1. Support for embedded arrays.

   Many languages use a combined structure consisting of a fixed set of fields together with an array. This is, for example, how arrays themselves are realized in languages like Java.
   
   Potentially restricted to a single embedded array.
   
1. Support for mutual access to structures from Wasm and from JavaScript.
   Note that we restrict ourselves here to accessing Wasm GC structures from JavaScript; we do not include here access to normal JavaScript objects from Wasm. This is already possible, albeit mediated by suitable function imports.
   
1. Support for parametric polymorphic types.
   Specifically, support for languages that support parametric type polymorphism; and subtype polymorphism. 
   The primary task of the Wasm type system is to be able to reliably and securely identify the representations of values. As such, it is not clear that Wasm's type system needs to be polymorphic. However, many statically typed languages are polymorphic, and there are multiple strategies for realizing them -- from a so-called uniform representation (for representing parametric types) to compile-time monomorphization.
   
1. Support for multi-threading. 
   Multi-threaded execution is important for many languages. There are several combinations that need to be supported, two of which are: multiple threads accessing shared objects and multiple threads which are not permitted to share objects. 
   
   Furthermore, it must be the case that multiple threading in Wasm-GC does not inadvertently introduce shared access to objects from multiple JavaScript threads. 
   
   This requirement, however, focuses on the need to ensure compatibility with Wasm-GC and any further development of Wasm threading.
   

### Non-Requirements
1. Arbitrary interoperability between different languages on the wasm.
   While it may be tempting to try to support arbitrary interoperability across languages -- by enabling cross language access to data structures in the case of Wasm-GC -- this is fraught with many difficulties; not the least of which are caused by those languages themselves.
   The task of Wasm-GC is to enable managed languages to represent their structures in such a way as can be managed by the host. This does not imply interoperability between languages or between languages and the host.
1. Arbitrary interoperability with host.
   Similar to the above issue.
1. Support for language specific constraints on garbage collection. For example, some reference counted languages attempt to guarantee that garbaged structures are immediately cleaned up.

## Phased Release
It is unlikely that Wasm-GC will be released as a single version. A more approachable strategy involves releasing subsets of the final proposal over time. 

The driver for a given release is the set of applications and capabilities that are unlocked by a given feature set; and their importance.

Without determining a specific road map here, we establish criteria for individual phases of the road map:

1. Each phase should be additive to prior phases.
1. Each phase should identify which scenarios are unlocked by the new features.


