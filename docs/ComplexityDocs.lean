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

The executable backend is word-RAM. Both its structured programming interface
and an [independent typed source language](##Complexity.Language.Basic) are available;
shared compilation proofs connect source contracts to the same actual RAM code.
This does not compile arbitrary Lean functions or require per-program register proofs.

`source_program (pure)` generates native total scalar functions and checked
source correspondence. [Factorial](##Examples.Language.Factorial) uses ordinary
mathematical induction and one native termination argument; Scalar and Remainder
use the same interface. This pure subset supports self-recursion and acyclic calls,
not pure `while`, mutual recursion or buffers.

The effectful surface supports mutable locals, shared buffers, loops, calls and
`Buffer.alloc`. Source correctness uses mathematical contents and native VCG rules,
without a capacity or time budget. The [allocation client](##Examples.Language.Allocation)
allocates in a callee, returns a buffer, allocates again and reads the original.
[Generic counted transfer](##Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution)
reaches its halted RAM invocation with actual heap, cursor and returned contents,
including internal and outer-call overheads. Word ranges, rooted represented inputs
and code/stack/arena capacity remain separate backend conditions. Input preparation
and session bootstrap are separate operations; the monotone arena has no reclamation.
The [source-frame rule](##Complexity.Language.Effects.Heap) preserves existing contents
through allocating code and callees without explicit cell writes, including finite faults.
Further resource inference and richer pure data/loop interfaces remain future work.

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
