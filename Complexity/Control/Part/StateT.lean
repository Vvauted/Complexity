/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Control.Part
import Std.Do.Triple.Basic

/-!
# Native specifications for partial state computations

These adequacy rules connect ordinary result/state equations to the existing
strict `Std.Do` interpretation of `StateT σ Part`. They retain the actual final
state and require a finite result; they introduce no evaluator or alternative
weakest-precondition interface.
-/

namespace Part.TotalCorrectness

open Std.Do
open scoped Part.TotalCorrectness

universe u

/-- A native state triple is precisely finite success with its postcondition
at the actual returned value and final state. -/
theorem stateT_triple_iff {σ α : Type u} (action : StateT σ Part α)
    (pre : σ → Prop) (post : PostCond α (.arg σ .pure)) :
    Triple action (fun state => ⟨pre state⟩) post ↔
      ∀ state, pre state → ∃ value finish,
        action state = Part.some (value, finish) ∧ (post.1 value finish).down := by
  simp only [Triple, WP.wp, PredTrans.pushArg, Part.TotalCorrectness.wp]
  constructor
  · intro specification state input
    obtain ⟨⟨value, finish⟩, member, property⟩ := specification state input
    exact ⟨value, finish, Part.eq_some_iff.mpr member, property⟩
  · intro specification state input
    obtain ⟨value, finish, executed, property⟩ := specification state input
    exact ⟨(value, finish), Part.eq_some_iff.mp executed, property⟩

/-- Reuse an actual finite state-transition equation in a native continuation
specification without unfolding its weakest precondition. -/
theorem stateT_triple_of_eq {σ α : Type u} {action : StateT σ Part α}
    {entry finish : σ} {value : α} {post : PostCond α (.arg σ .pure)}
    (executed : action entry = Part.some (value, finish))
    (property : (post.1 value finish).down) :
    Triple action (fun state => ⟨state = entry⟩) post := by
  apply (stateT_triple_iff action _ post).mpr
  intro state same
  subst state
  exact ⟨value, finish, executed, property⟩

/-- Apply a native specification to the actual observed result and state.
The existing partial computation has at most one result, so a consumer need
not repeat the specification's termination or result-uniqueness proof. -/
theorem stateT_post_of_eq {σ α : Type u} {action : StateT σ Part α}
    {pre : σ → Prop} {post : PostCond α (.arg σ .pure)}
    (specification : Triple action (fun state => ⟨pre state⟩) post)
    {entry finish : σ} {value : α} (initial : pre entry)
    (executed : action entry = Part.some (value, finish)) :
    (post.1 value finish).down := by
  obtain ⟨actualValue, actualFinish, actual, property⟩ :=
    (stateT_triple_iff action pre post).mp specification entry initial
  rcases Prod.mk.inj (Part.some_injective (actual.symm.trans executed)) with ⟨rfl, rfl⟩
  exact property

end Part.TotalCorrectness
