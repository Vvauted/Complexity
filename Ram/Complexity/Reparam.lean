/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity

/-!
# Changing the size parameter of a verified runtime bound

The code, input encoding, admissible input family, postcondition, and exact
runtime witness are unchanged. Only the size filter and comparison function
change. The old size must tend to infinity along the new size filter: an
asymptotic bound for large old sizes says nothing about a bounded old subsize.

These are transports of the existing `UniformBigO` via mathlib's filter and
asymptotic lemmas, not new complexity definitions or encoding conversions.
-/

namespace Ram.UniformBigO

variable {Input : Type} {code : Code}
variable {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
variable {size newSize : Input → Nat} {post : ∀ w, Input → State w → Prop}
variable {growth newGrowth : Nat → Nat}

/-- Transport the same correctly terminating runtime witness to a new size
parameter. The two premises respectively transport the old asymptotic domain
and compare its growth bound to the requested new one. -/
theorem reparam (h : UniformBigO code encode admissible size post growth)
    (hsize : Filter.Tendsto (fun i : LegalInput admissible => size i.val.2)
      (inputSizeFilter admissible newSize) Filter.atTop)
    (hgrowth : Asymptotics.IsBigO (inputSizeFilter admissible newSize)
      (fun i => (growth (size i.val.2) : ℝ))
      (fun i => (newGrowth (newSize i.val.2) : ℝ))) :
    UniformBigO code encode admissible newSize post newGrowth := by
  obtain ⟨runtime, hrun, hbound⟩ := h
  exact ⟨runtime, hrun, (hbound.mono hsize.le_comap).trans hgrowth⟩

/-- When the old size is a function of the new one, the premises can be proved
entirely on natural sizes. The explicit `Tendsto` condition prevents applying
an old large-input certificate through a bounded size transformation. -/
theorem reparam_of_comp {changeSize : Nat → Nat}
    (h : UniformBigO code encode admissible (changeSize ∘ newSize) post growth)
    (hsize : Filter.Tendsto changeSize Filter.atTop Filter.atTop)
    (hgrowth : Asymptotics.IsBigO Filter.atTop
      (fun n => (growth (changeSize n) : ℝ)) (fun n => (newGrowth n : ℝ))) :
    UniformBigO code encode admissible newSize post newGrowth :=
  h.reparam (hsize.comp Filter.tendsto_comap)
    (hgrowth.comp_tendsto Filter.tendsto_comap)

end Ram.UniformBigO
