/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.Merge
import Ram.Complexity.Polynomial

/-!
# Linear complexity of the verified merge block

`Merge.contract` proves at most `34 * (xs.length + ys.length) + 4`
actual compiled steps. The checked preloaded block adds one halt transition.
These lemmas expose mathlib's asymptotic bound for that same budget, measured
in source-array words. They do not include a loader or destination allocation.
-/

namespace Ram.Source.Array.Merge

/-- One coefficient bounds the actual block budget, including its final halt,
also for two empty inputs. It is independent of contents and word width. -/
theorem budget_add_halt_le_shifted (n : Nat) : 34 * n + 5 ≤ 34 * (n + 1) := by
  omega

/-- Mathlib's `IsBigO` for the bound established by the merge execution contract,
with the total source length as size and one additional halt transition. -/
theorem budget_isBigO :
    Asymptotics.IsBigO Filter.atTop (fun n => ((34 * n + 5 : Nat) : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) := by
  simpa only [pow_one] using
    (isBigO_shifted_pow_iff (f := fun n => 34 * n + 5) (k := 1)).mpr
      ⟨34, fun n => by simpa only [pow_one] using budget_add_halt_le_shifted n⟩

end Ram.Source.Array.Merge
