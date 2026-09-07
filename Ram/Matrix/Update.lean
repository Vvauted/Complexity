/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Equivalent single-entry matrix updates

Updating one entry through its column or its row produces the same ordinary
mathlib matrix. The simplification rule chooses the row-update form, allowing
representation and native stateful proofs to reuse the same mathematical model.
This module depends only on mathlib and has no RAM-specific assumptions.
-/

namespace Matrix

/-- Updating one entry through its column agrees with updating it through its row. -/
@[simp]
theorem updateCol_update {m n α : Type*} [DecidableEq m] [DecidableEq n]
    (A : Matrix m n α) (i : m) (j : n) (value : α) :
    A.updateCol j (Function.update (fun r => A r j) i value) =
      A.updateRow i (Function.update (A i) j value) := by
  funext r c
  by_cases hr : r = i <;> by_cases hc : c = j <;>
    simp [updateRow_apply, hr, hc]

end Matrix
