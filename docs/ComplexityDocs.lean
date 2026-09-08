/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import ComplexityDocs.Backend
import ComplexityDocs.Complexity
import ComplexityDocs.Development
import ComplexityDocs.GettingStarted
import ComplexityDocs.Models
import ComplexityDocs.Verification

/-!
# Complexity

Complexity is a Lean library for verified programming and complexity analysis.
This manual explains how to use its current interfaces. The API reference is generated
from the same source files; use the search box to find a declaration or the module tree
to browse a topic.

## Start here

1. [Getting started](##ComplexityDocs.GettingStarted): define and run a function,
   then prove a mathematical property of its result.
2. [Proving correctness](##ComplexityDocs.Verification): specifications, total correctness,
   calls, loops and reuse of ordinary Lean proofs.
3. [Working with data](##ComplexityDocs.Models): arrays, mathematical views and memory frames.
4. [Proving complexity](##ComplexityDocs.Complexity): separate cost proofs, mathematical bounds
   and complete executable certificates.

For machine assumptions and compiler details, see
[the execution backend](##ComplexityDocs.Backend). For builds, module layout and contributing
documentation, see [development](##ComplexityDocs.Development).

## What is available

The complete executable workflow currently uses a structured word-RAM language with
named variables, functions and recursion. Correctness proofs can use mathematical
relations, pure Lean functions or native
`StateM` specifications. The implementation-to-model connection is still an explicit proof;
ordinary Lean functions are not automatically compiled into RAM programs.

An [independent scalar core](##Complexity.Language.Basic) and
[source correctness rules](##Complexity.Language.Verification) are also available.
They support a mathematical proof of a real helper-call/branch program without
registers; its Lean-like surface and whole-function compiled proof transfer are
still under development. See [the scalar example](##Examples.Language.Scalar).

Functions can be declared without a `main` and verified through their arguments,
returned value and shared effects. Start with the
[function contracts](##Complexity.Computability.Ram.Verification.Function);
[function costs](##Complexity.Computability.Ram.Source.Function.Time) observe the same
implementation separately from a proposed bound.

The [function runner](##Examples.Ram.FunctionRun) executes a compiled call without
an I/O driver or a supplied instruction limit. The
[array-argument sample](##Examples.Ram.ArrayArguments) composes two typed array calls
and describes the result with ordinary lists. Array references describe preloaded
data; they do not implicitly convert or allocate Lean lists in the machine heap.

Reusable programs can be packaged and linked without a time budget using
[total components](##Complexity.Computability.Ram.Component.Total), then receive separate
time proofs for the same code.

Numerical bounds can be used independently of the machine. Start with
[polynomial growth](##Complexity.Analysis.Asymptotics.Polynomial),
[recurrences](##Complexity.Computability.Recurrence.Basic) or
[amortized sums](##Complexity.Analysis.Amortized).

The [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md) describes
the remaining work on source-level proof interfaces, operation composition and resource theory.
-/
