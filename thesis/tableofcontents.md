# Introduction

- Why bother with correctness of programs in general?
- Why bother with *correctness* of language implementations?
- Bridge between specification (in our case, a big-step semantics) and an execution model (i.e, an abstract machine or interpreter)
- etc.

# Background

## Propositions as Types

- Could elaborate on what is really meant by a proof.
- Touch on classical logic vs constructive logic, which leads us to:

## Agda

- Dependent Types
- Touch on Curry-Howard Isomorphism, and how we encode (classical) logic into types.
- Micro-tutorial/overview on Agda?

# Programming Languages / Semantics

- Syntax (defined in Agda)
  - Contexts + Debrujin Indices for vars
  - Intrinsic/Extrinsic typing
- Semantics
  - Denotational, small-steps
  - Big-step
  - The abstract machine, and the approach used to 'derive' it.
- Related Work:
  - Programming Language Semantics, it's as easy as 1,2,3.
  - Dissecting Data Structures.
  - Edgard's Report(?)
  - ...
- Incremental Additions to a language:
  - Base: STLC
  - STLC -(+ LetRec)-> PCF
  - PCF -(+ Prods, Sums, +Exceptions?) -> MicroML.
  - MicroML -> ?

## Conclusion

- Recap
- Outlook:
  - Reasoning about non-terminating programs i.e, hoare logic; coinductive semantics)?
  - Extensions to the languages (Algebraic Effects? Mutable State? Concurrency?)
  - Automating the derivation of the abstract machine?

## References (so far)

- TAPL
- PLFA
- Literature mentioned in the related works section.
