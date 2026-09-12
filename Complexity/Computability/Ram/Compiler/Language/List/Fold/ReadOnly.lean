/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Fold.Program
import Complexity.Computability.Ram.Compiler.Language.Linking.Effects

/-!
# Read-only effects of the shared list fold

The traversal itself reads immutable nodes and changes locals. When all bodies
in the original callback program are read-only, its actual extension by the
shared fold is read-only as well. Clients reuse this structural theorem instead
of unfolding the traversal or reproving any source execution.
-/

namespace Ram.LanguageCompiler.List.Fold

open Complexity.Language

variable {signatures : _root_.List Signature} {accTy : Ty} {kind : CellTy}

/-- The traversal has no direct writes; its callback is checked separately. -/
theorem body_noHeapWrites (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind) :
    NoHeapWrites (Complexity.Language.List.Fold.body fn same) := by
  simp only [Complexity.Language.List.Fold.body, Complexity.Language.List.Fold.loop,
    Complexity.Language.List.Fold.guard, Complexity.Language.List.Fold.iteration,
    NoHeapWrites, noHeapWrites_callOfEq, and_self]

/-- Adding the actual shared fold preserves the whole program's read-only
condition, including the original callback's recursive and internal calls. -/
theorem program_noHeapWrites (source : Complexity.Language.Program signatures)
    (fn : Fin signatures.length)
    (same : signatures[fn] = Complexity.Language.List.Fold.stepSignature accTy kind)
    (readOnly : ∀ index, NoHeapWrites (source.body index)) :
    ∀ index, NoHeapWrites ((Complexity.Language.List.Fold.program source fn same).body index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · change NoHeapWrites ((Complexity.Language.List.Fold.program source fn same).body
      (Complexity.Language.List.Fold.entry accTy kind signatures))
    rw [Complexity.Language.List.Fold.program_body]
    exact body_noHeapWrites _ _
  · intro original
    have indexEq : original.succ =
        Complexity.Language.List.Fold.calleeEntry accTy kind original := by
      apply Fin.ext
      change original.val + 1 = 1 + original.val
      exact Nat.add_comm _ _
    rw [indexEq]
    exact noHeapWrites_mapped_body
      (Complexity.Language.List.Fold.program_embeds source fn same) original (readOnly original)

end Ram.LanguageCompiler.List.Fold
