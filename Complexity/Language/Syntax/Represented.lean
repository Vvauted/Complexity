/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Represented.Elab

/-!
# Native mathematical views of represented source operations

This frontend retains ordinary mathematical types alongside actual source types.
Heap-backed arrays and lists carry relations, not heap-independent encodings.
Mutable local versions, conditionals and normal finite ranges compose the same
registered operations and their checked heap relations. A finite range retains
the shared source's original named loop and in-place body; its mathematical fold
is proof-side only. General while and source calls without a total model retain
their actual control and heap effects, exposing source contracts instead of a
fabricated pure function. Value-producing branches use the shared source's local
return boundary, including loops and scratch scopes; exit-controlled ranges
retain source control without an automatic total-function view. Shared typed product
and Option patterns retain one evaluation and ordinary source projections.
Scratch blocks retain their real cleanup and enclosing returns; their contracts
observe the post-cleanup heap rather than a pre-cleanup mathematical view.
-/
