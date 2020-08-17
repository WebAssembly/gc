# Requirements for GC

## Goals

1. Support for host-provided GC

   Allow language implementers to use host-provided GC features as their primary means of supporting memory management.
   
## Critical Success Factors

1. Permit ‘cycle detection’ between host structures and language structures; so that such cycles can be collected if there are no other references to them.
1. Performance of host GC should be comparable with performance of equivalent ‘linear GC’ solutions. 
1. Permit access to language structures from host.

## Requirements

1. Support for typical memory layouts employed by languages like Java/C#/Kotlin.
1. Support for V-tables for object layout.

## Non-Requirements
1. Arbitrary interoperability with different languages on the wasm.
1. Arbitrary interoperability with host language.
1. Permit access to host data structures from wasm.
