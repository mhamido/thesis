# Deriving Interpreters: From Big-Step SOS to Abstract Machines

This repository contains the source code of all things related to my master's thesis, at RPTU KL.

## Abstract

Implementations of programming languages are expected to faithfully realize their specifications, yet in practice, this correspondence is often validated only by testing against written standards or reference implementations. Since testing ranges over finitely many programs, it cannot establish the absence of mismatches for all well-typed inputs. This thesis develops a machine-checked approach in Agda in which an implementation is systematically derived from its formal semantics and proved correct by construction. We present a uniform derivation of abstract machines from semantic definitions, carried out for three case studies: arithmetic expressions, arithmetic expressions with exceptions, and the simply typed lambda calculus. The derivation makes evaluation structure explicit via typed frames and a stack of machine states, with operational modes for evaluation and return, and an additional unwind mode for exceptions. For each language, transition rules are obtained by mimicking in-order evaluation, and the resulting machine is proved correct and complete with respect to big-step semantics.

[Thesis](./thesis/thesis.pdf)

## Overview

The `./code` directory houses all the Agda files.

- `Arith`, `Exception`, and `STLC` present the derivation described in the thesis. Each language contains 5 scripts, for each semantics. Recommended Reading Order:
  1. `Definitions.lagda`
  2. `Big-Step.lagda`
  3. `Machine.lagda`
  4. `Small-Step.agdai`
  5. `Denotational.lagda`

- `STLC-Alt` contains an alternative presentation of the STLC language, which embeds closures into the syntax tree via the quote (`) constructor. This is kept around just to show the difficulty of bridging the substitution-based small-step semantics with our notion of environments used in all other semantics.

There are also 2 additional languages for which only the big-step semantics and abstract machines are defined. These are not directly addressed in the thesis, but were a part of it nonetheless.

- [LambdaErr](./code/LambdaErr.lagda) is an extension of the STLC with exceptions. Initially, this was the earliest language I intended to use in the thesis to demonstrate exceptions.

 However, since exceptions are orthogonal to the functional aspects of STLC, it would be clearer to present a simpler version of a language with exceptions.

- [Milli](./code/Milli.lagda) is an exception of STLC with a fix point operator, products, and sum types. This was a brief excursion into testing our derivation method on other language features.

There was also a brief excursion into whether we could reason about non-terminating programs, but not much progress has been made there by virtue of using an inductive big-step relation.
