/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization.WP
import Complexity.Language.Eval.Locals.LocalReturn

/-!
# Realizing a completed local block's loop guard

A saved local result bypasses the original guard. The actual option match still
binds its payload, so that payload must fit the selected word width. The false
return leaves the complete outer state unchanged, without assumptions about the
original guard's execution or its operation ranges.
-/

namespace Ram.LanguageCompiler.RealizationWP

open Complexity.Language

/-- The real completed branch checks the saved payload's range and returns
false with the same locals and heap. It neither evaluates the original test nor
uses any call nesting or arena capacity. -/
theorem localReturn_guard_some {signatures : List Signature} {Γ : List Ty} {τ : Ty}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {pending : Atom Γ (.option τ)} {test : Complexity.Language.Stmt signatures Γ .bool}
    {entry : Complexity.Language.State Γ} {value : Value τ}
    (stopped : pending.eval entry.locals = some value) (fits : ValueFits w value) :
    RealizationWP program w depth (Stmt.LocalReturn.guard pending test)
      (fun _ => False) (fun decision finish => decision = false ∧ finish = entry) entry := by
  rw [Stmt.LocalReturn.guard, matchOption_iff, stopped]
  refine ⟨fits, ?_⟩
  rw [ret_iff]
  exact ⟨Nat.two_pow_pos w, rfl, rfl⟩

end Ram.LanguageCompiler.RealizationWP
