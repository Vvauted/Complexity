/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Init.Data.Array.MapIdx
import Lean.Elab.Tactic.Omega

/-!
# Updating an indexed mapped prefix

One native array update advances the boundary between a transformed prefix and
an unchanged suffix. The statement uses ordinary `Array.mapIdx` and `Array.set`;
it does not define a traversal implementation or a separate container.
-/

namespace Array

universe u

/-- Transforming the next unchanged element advances the mapped prefix by one. -/
theorem set_mapIdx_ite_lt {α : Type u} (f : α → α) {xs : Array α} {i : Nat}
    (hi : i < xs.size) :
    (xs.mapIdx (fun j x => if j < i then f x else x)).set i (f xs[i])
        (by simpa only [size_mapIdx] using hi) =
      xs.mapIdx (fun j x => if j < i + 1 then f x else x) := by
  apply ext (by simp)
  intro j leftBound rightBound
  simp only [getElem_set, getElem_mapIdx]
  by_cases same : i = j
  · subst j
    simp
  · have next : j < i + 1 ↔ j < i := by omega
    simp only [if_neg same, next]

end Array
