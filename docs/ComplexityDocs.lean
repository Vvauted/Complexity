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
# Complexity manual

Complexity develops programming and proof infrastructure for functional correctness and
resource complexity in Lean. This manual explains the implemented interfaces; the
[roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md) describes the larger goal
of ordinary high-level programming with verified lowering and reusable cost proofs.

The current executable language is a structured word-RAM language. Its compiler, mathematical
model interfaces and complexity library support useful separation between algorithmic
reasoning and machine reasoning. A general single-source high-level frontend is not yet
implemented: arbitrary Lean functions do not automatically become executable machine code.

An ordinary `StateM` computation is an optional mathematical model, not a required second
program that every user must write and maintain. Pure Lean functions and direct contracts
are also supported. Model implementations supplied by the library can be reused without
reproving their memory layout, calling convention or compiler simulation.

## Reading the manual

1. [Getting started](##ComplexityDocs.GettingStarted): installation, imports, source syntax,
   execution and existing examples.
2. [Functional verification](##ComplexityDocs.Verification): total correctness, mathematical
   specifications, native Lean verification, calls, control flow and proof automation.
3. [Data models and memory](##ComplexityDocs.Models): choosing mathlib objects, updating them,
   composing stateful operations and preserving unrelated data.
4. [Complexity proofs](##ComplexityDocs.Complexity): separate time bounds, amortization,
   recurrences, asymptotics, component composition and complete problem claims.
5. [Execution backend](##ComplexityDocs.Backend): machine assumptions, compilation, calls,
   observation boundaries and resource measurements.
6. [Dependencies and documentation](##ComplexityDocs.Development): mathlib reuse, builds
   and documentation maintenance.

Use `import Complexity` for the public library, or a specific `Complexity.*` module for
a smaller dependency set. RAM declarations use the namespace `Ram`, but belong to this
same library. The manual and examples are separate consumers, not required imports.

## Choosing an entry point

| Task | Start with |
| --- | --- |
| Prove what a program computes | `Ram.Source.TotalContract`, `Ram.Source.Refines` |
| Verify a mathematical stateful model | `Std.Do.Triple`, [native refinement](##Complexity.Computability.Ram.Verification.StateM.Basic) |
| Reuse an array, matrix or map implementation | [Data models](##ComplexityDocs.Models) |
| Prove a time bound independently | `Ram.Source.TimeBound` |
| Analyze numerical bounds | [Recurrences](##Complexity.Computability.Recurrence.Basic), [polynomial growth](##Complexity.Analysis.Asymptotics.Polynomial) |
| Connect a bound to machine runtime | [Uniform time bounds](##Complexity.Computability.Ram.Time.Basic) |
| Link separately verified implementations | `Ram.Component` |
| Understand the machine/compiler boundary | [Execution backend](##ComplexityDocs.Backend) |

The project is AI-assisted and contains substantial AI-generated code, proofs and prose.
See the [project overview](https://github.com/Vvauted/Complexity) for its AIGC disclosure.
Lean checking establishes the formal theorems; it does not replace review of whether their
statements, representations and machine assumptions express the intended claims.
-/
