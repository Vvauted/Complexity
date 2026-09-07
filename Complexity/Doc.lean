/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Doc.GettingStarted
import Complexity.Doc.Verification
import Complexity.Doc.Models
import Complexity.Doc.Complexity
import Complexity.Doc.Backend
import Complexity.Doc.Integration

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

1. [Getting started](##Complexity.Doc.GettingStarted): installation, imports, source syntax,
   execution and existing examples.
2. [Functional verification](##Complexity.Doc.Verification): total correctness, mathematical
   specifications, native Lean verification, calls, control flow and proof automation.
3. [Data models and memory](##Complexity.Doc.Models): choosing mathlib objects, updating them,
   composing stateful operations and preserving unrelated data.
4. [Complexity proofs](##Complexity.Doc.Complexity): separate time bounds, amortization,
   recurrences, asymptotics, component composition and complete problem claims.
5. [Execution backend](##Complexity.Doc.Backend): machine assumptions, compilation, calls,
   observation boundaries and resource measurements.
6. [Dependencies and documentation](##Complexity.Doc.Integration): mathlib reuse, optional
   CSLib integration, builds and documentation maintenance.

Use `import Complexity` for the public library. The existing backend API remains under
`Ram`; importing a particular `Ram` module gives a smaller dependency set. The manual is
separate from the library entry point, so ordinary clients do not import documentation.

## Choosing an entry point

| Task | Start with |
| --- | --- |
| Prove what a program computes | `Ram.Source.TotalContract`, `Ram.Source.Refines` |
| Verify a mathematical stateful model | `Std.Do.Triple`, `Ram.Verification.StateM` |
| Reuse an array, matrix or map implementation | [Data models](##Complexity.Doc.Models) |
| Prove a time bound independently | `Ram.Source.TimeBound` |
| Analyze sums, recurrences or asymptotics | `Ram.Complexity`, `Ram.Complexity.Recurrence` |
| Link separately verified implementations | `Ram.Component` |
| Understand the machine/compiler boundary | [Execution backend](##Complexity.Doc.Backend) |

The project is AI-assisted and contains substantial AI-generated code, proofs and prose.
See the [project overview](https://github.com/Vvauted/Complexity) for its AIGC disclosure.
Lean checking establishes the formal theorems; it does not replace review of whether their
statements, representations and machine assumptions express the intended claims.
-/
