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

1. [Getting started](ComplexityDocs/GettingStarted.html): define and run a function,
   then prove a mathematical property of its result.
2. [Proving correctness](ComplexityDocs/Verification.html): specifications, total correctness,
   calls, loops and reuse of ordinary Lean proofs.
3. [Working with data](ComplexityDocs/Models.html): arrays, mathematical views and memory frames.
4. [Proving complexity](ComplexityDocs/Complexity.html): separate cost proofs, mathematical bounds
   and complete executable certificates.

For a fixed mathematical input/output task, see
[program specifications](ComplexityDocs/GettingStarted/Programs.html). The correctness guide
has separate chapters on [source proof views](ComplexityDocs/Verification/Source.html),
[represented data](ComplexityDocs/Verification/Representations.html),
[mutable contracts](ComplexityDocs/Verification/State.html),
[loops and recursion](ComplexityDocs/Verification/Loops.html), and
[the RAM connection](ComplexityDocs/Verification/Compilation.html).
The direct word-RAM interface has its own
[programming guide](ComplexityDocs/GettingStarted/WordRam.html),
[execution guide](ComplexityDocs/GettingStarted/Execution.html), and
[contract reference](ComplexityDocs/Verification/Ram/Contracts.html).

For machine assumptions and compiler details, see
[the execution backend](ComplexityDocs/Backend.html). For builds, module layout and contributing
documentation, see [development](ComplexityDocs/Development.html).

## What is available

The executable backend is word-RAM. Both its structured programming interface
and an [independent typed source language](##Complexity.Language.Basic) are available;
shared compilation proofs connect source contracts to the same actual RAM code.
This does not compile arbitrary Lean functions or require per-program register proofs.

The recommended declaration is `source_program P where`. It exposes the actual
source action and, when available, a checked total mathematical model.
[Scalar](##Examples.Language.Scalar) uses ordinary equations about that model;
[Factorial](##Examples.Language.Factorial) retains the `(pure)` compatibility
interface and uses mathematical induction with one native termination argument.
General mutable programs use state contracts, not an invented pure total model.
The [source proof guide](ComplexityDocs/Verification/Source.html) explains this boundary.

The effectful surface supports mutable locals, shared buffers, loops, calls and
`Buffer.alloc` and `with_scratch` scopes. Source correctness uses mathematical
contents and native VCG rules,
without a capacity or time budget. The [allocation client](##Examples.Language.Allocation)
allocates in a callee, returns a buffer, allocates again and reads the original.
[Generic counted transfer](##Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution)
reaches its halted RAM invocation with actual heap, cursor and returned contents,
including internal and outer-call overheads. Word ranges, rooted represented inputs
and code/stack/arena capacity remain separate backend conditions. Input preparation
and session bootstrap are separate operations. Scratch scopes preserve current
writes to older objects while reclaiming temporary allocations; longer-lived
outputs must remain outside the reclaimed region. The source checks escaping
handles, and the compiled success guarantee requires proved-safe exits.
The [scoped source consumer](##Examples.Language.Scope) proves nested/called
cleanup and a retained result. Its visible completion contracts hide private
result slots, and its loop uses Lean's `measure` only for continuing iterations.
Its [compiled workspace theorem](##Examples.Language.ScopeCompiled) bounds all
actual accesses independently of repetition count, including both call frames.
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
