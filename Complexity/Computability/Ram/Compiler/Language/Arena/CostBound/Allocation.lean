/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Structural cost of initialized buffer allocation

This rule bounds the existing allocation cost observation. The continuation
starts at `Heap.alloc`'s actual initialized heap and returned descriptor, while
the allocator's operand preparation, reservation and initialization retain the
count already established by the measured compiler theorem. The rule supplies
neither a successful execution nor a new capacity or word-range assumption.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

/-- Compose the measured allocator's real initialization charge with a bound
on its continuation at the actual freshly extended source heap. -/
theorem alloc {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty} {kind : CellTy}
    {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {entry : Complexity.Language.State Γ} {bound : Nat}
    (body : StmtArenaCostBound program w heapLimit depth continuation
      (let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))
       Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩) bound) :
    StmtArenaCostBound program w heapLimit depth (.alloc length initial continuation) entry
      (14 * length.eval entry.locals + 18 + bound) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | alloc tail => exact Nat.add_le_add_left (body _ _ tail) _

end Ram.LanguageCompiler.StmtArenaCostBound
