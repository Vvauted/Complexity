/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured

/-!
# Composing actual measured allocation

The allocation rule retains the initialized source object, its actual extended
heap, and the increased arena cursor for the continuation. Its instruction count
is the existing allocation constructor's count, not a user-selected budget.
-/

namespace Ram.LanguageCompiler.ArenaMeasured

open Complexity.Language

/-- Allocate the actual initialized array, then continue at its extended heap and
cursor. Initialization work is included by the existing compiler cost rule. -/
theorem alloc {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {kind : CellTy}
    {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (initialFits : ValueFits w (initial.eval entry.locals))
    (capacity : cursor + length.eval entry.locals ≤ heapLimit)
    (body :
      let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))
      ArenaMeasured program w heapLimit depth continuation
        (fun finish control finalCursor steps =>
          post finish.tail control finalCursor (14 * length.eval entry.locals + 18 + steps))
        (Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩)
        (cursor + length.eval entry.locals)) :
    ArenaMeasured program w heapLimit depth (.alloc length initial continuation)
      post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish.tail, control, finalCursor, _, Complexity.Language.Exec.alloc execution,
    ArenaReady.alloc initialFits capacity ready,
    ArenaExecutionCost.alloc (initialFits := initialFits) (capacity := capacity) cost, outcome⟩

end Ram.LanguageCompiler.ArenaMeasured
