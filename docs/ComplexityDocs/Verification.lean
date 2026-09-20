/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import ComplexityDocs.Verification.Compilation
import ComplexityDocs.Verification.Lists
import ComplexityDocs.Verification.Loops
import ComplexityDocs.Verification.Ram.Automation
import ComplexityDocs.Verification.Ram.Contracts
import ComplexityDocs.Verification.Ram.Models
import ComplexityDocs.Verification.Representations
import ComplexityDocs.Verification.Source
import ComplexityDocs.Verification.State

/-!
# Proving correctness

Start with the mathematical result you want, then connect it to the implementation.
The correctness interface includes safety and termination, but asks for no time budget.
A separate [complexity proof](ComplexityDocs/Complexity.html) can reuse the same invariants.

## Source-level proofs

Start with the proof view that matches the program. A total mathematical model supports ordinary
Lean equations; mutation uses contracts about mathematical contents and the actual endpoint heaps.
Both views describe the same declared implementation.

- [Source semantics and proof views](ComplexityDocs/Verification/Source.html)
- [Represented data and collection contracts](ComplexityDocs/Verification/Representations.html)
- [Proving linked-list programs](ComplexityDocs/Verification/Lists.html)
- [Mutable state, scratch scopes and calls](ComplexityDocs/Verification/State.html)
- [Source loops and recursion](ComplexityDocs/Verification/Loops.html)
- [Connecting source proofs to RAM](ComplexityDocs/Verification/Compilation.html)

## Direct word-RAM proofs

The direct RAM language remains available for backend work and explicitly low-level
implementations. These chapters use its word arithmetic, representations and source contracts:

- [Direct word-RAM contracts and execution](ComplexityDocs/Verification/Ram/Contracts.html)
- [Mathematical models for word-RAM programs](ComplexityDocs/Verification/Ram/Models.html)
- [Direct word-RAM proof automation and composition](ComplexityDocs/Verification/Ram/Automation.html)

## Related chapters

- [Getting started](ComplexityDocs/GettingStarted.html): declarations and executable entry points.
- [Working with data](ComplexityDocs/Models.html): representations, aliasing and memory frames.
- [Proving complexity](ComplexityDocs/Complexity.html): separate bounds for the same execution.
- [Execution backend](ComplexityDocs/Backend.html): machine assumptions and counting boundaries.
- [Development](ComplexityDocs/Development.html): builds and module organization.
-/
