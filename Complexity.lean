/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram

/-!
# Complexity

Verified programming and complexity proofs in Lean.

This is the public entry point of the Complexity package. The current verified
implementation and its proof interfaces live in `Ram`; these names identify the
word-RAM backend and remain available to existing clients. A project-level entry
point does not by itself make those interfaces independent of a machine model.

The user guide is in `Complexity.Doc`. It distinguishes available programming,
verification and resource interfaces from the high-level frontend described in
the [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md).
Examples can be imported separately through `Ram.Examples`.
-/
