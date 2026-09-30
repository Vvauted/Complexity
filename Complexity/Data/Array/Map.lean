/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.Array.Lemmas
import Mathlib.Logic.Embedding.Basic

/-!
# Injective array maps and defaulted lookup

Mapping an injective element view preserves array identity. Defaulted lookup
commutes with mapping when the supplied default is mapped as well.
-/

namespace Function.Embedding

/-- Lift an injective element view without changing array order or length. -/
def arrayMap {α : Type u} {β : Type v} (view : α ↪ β) : Array α ↪ Array β where
  toFun := Array.map view
  inj' := fun _ _ same => (Array.map_inj_right (fun _ _ h => view.injective h)).mp same

end Function.Embedding

namespace Array

/-- Mapping a defaulted lookup maps its default as well as its selected element. -/
theorem getD_map {α : Type u} {β : Type v} (f : α → β) (xs : Array α)
    (index : Nat) (fallback : α) :
    (xs.map f).getD index (f fallback) = f (xs.getD index fallback) := by
  by_cases bound : index < xs.size <;> simp [Array.getD, bound]

end Array
