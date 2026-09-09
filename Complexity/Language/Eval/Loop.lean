/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Verification

/-!
# Native observations and total correctness of source loops

`Stmt.action_while` unfolds one iteration of the existing source loop observation.
It is a theorem about `Stmt.action`, not a recursively defined host loop or an
alternative algorithm. The guard and body both retain their actual final locals
and heap. A false guard exits at its updated state; a body return bypasses the
remaining iterations. Guard fallthrough is a finite missing-return fault.

`Stmt.while_spec` transports the source well-founded rule to native `Std.Do`
triples. Users supply an invariant and a well-founded decrease over the complete
guard/body cycle. Guard and body termination are included in their strict
specifications; neither a time budget nor a machine representation is involved.
-/

namespace Complexity.Language.Stmt

open scoped Part.TotalCorrectness

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable (program : Program signatures)

/-- One unfolding of the same source loop in native state-action notation.
This equation is deliberately not a simp rule: unrestricted unfolding would
keep unfolding the recursive loop observation. -/
theorem action_while (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result) :
    (Stmt.while guard body).action program = (do
      match ← guard.action program with
      | .returned false => pure .normal
      | .returned true =>
          match ← body.action program with
          | .normal => (Stmt.while guard body).action program
          | .returned value => pure (.returned value)
          | .fault error => pure (.fault error)
      | .normal => pure (.fault .missingReturn)
      | .fault error => pure (.fault error)) := by
  funext entry
  apply Part.ext
  rintro ⟨control, finish⟩
  simp only [Bind.bind, Pure.pure, StateT.bind]
  rw [mem_action_iff]
  constructor
  · intro execution
    cases execution with
    | whileFalse test =>
        exact Part.mem_bind (mem_action_iff.mpr test) (Part.mem_some_iff.mpr rfl)
    | whileTrue test iteration rest =>
        refine Part.mem_bind (mem_action_iff.mpr test) ?_
        simp only [Bind.bind, StateT.bind]
        exact Part.mem_bind (mem_action_iff.mpr iteration) (mem_action_iff.mpr rest)
    | whileReturn test iteration =>
        refine Part.mem_bind (mem_action_iff.mpr test) ?_
        simp only [Bind.bind, StateT.bind]
        exact Part.mem_bind (mem_action_iff.mpr iteration) (Part.mem_some_iff.mpr rfl)
    | whileFault test iteration =>
        refine Part.mem_bind (mem_action_iff.mpr test) ?_
        simp only [Bind.bind, StateT.bind]
        exact Part.mem_bind (mem_action_iff.mpr iteration) (Part.mem_some_iff.mpr rfl)
    | whileGuardFault test =>
        exact Part.mem_bind (mem_action_iff.mpr test) (Part.mem_some_iff.mpr rfl)
    | whileGuardMissingReturn test =>
        exact Part.mem_bind (mem_action_iff.mpr test) (Part.mem_some_iff.mpr rfl)
  · intro member
    obtain ⟨⟨guardControl, afterGuard⟩, guardMember, next⟩ := Part.mem_bind_iff.mp member
    have test := mem_action_iff.mp guardMember
    cases guardControl with
    | normal =>
        cases Part.mem_some_iff.mp next
        exact .whileGuardMissingReturn test
    | fault error =>
        cases Part.mem_some_iff.mp next
        exact .whileGuardFault test
    | returned again =>
        cases again with
        | false =>
            cases Part.mem_some_iff.mp next
            exact .whileFalse test
        | true =>
            simp only [Bind.bind, StateT.bind] at next
            obtain ⟨⟨bodyControl, afterBody⟩, bodyMember, rest⟩ := Part.mem_bind_iff.mp next
            have iteration := mem_action_iff.mp bodyMember
            cases bodyControl with
            | normal => exact .whileTrue test iteration (mem_action_iff.mp rest)
            | returned value =>
                cases Part.mem_some_iff.mp rest
                exact .whileReturn test iteration
            | fault error =>
                cases Part.mem_some_iff.mp rest
                exact .whileFault test iteration

/-- A native total-correctness rule for an effectful source loop. The guard
specification passes its actual state to the body specification. Only a normal
body completion must restore the invariant and decrease relative to the state
before the guard; early returns establish the requested result immediately. -/
@[spec] theorem while_spec (guard : Stmt signatures Γ .bool)
    (body : Stmt signatures Γ result) (invariant : State Γ → Prop)
    (relation : State Γ → State Γ → Prop) (wellFounded : WellFounded relation)
    (post : Std.Do.PostCond (Control result) (.arg (State Γ) .pure))
    (step : ∀ start, invariant start →
      Std.Do.Triple (m := StateT (State Γ) Part) (ps := .arg (State Γ) .pure)
        (guard.action program) (fun current => ⟨current = start⟩)
        (fun guardControl afterGuard => ⟨guardControl.Satisfies (fun _ => False)
          (fun again actual =>
            if again then
              Std.Do.Triple (m := StateT (State Γ) Part) (ps := .arg (State Γ) .pure)
                (body.action program) (fun current => ⟨current = actual⟩)
                (fun bodyControl afterBody => ⟨bodyControl.Satisfies
                  (fun next => invariant next ∧ relation next start)
                  (fun value finish => (post.1 (.returned value) finish).down) afterBody⟩, ⟨⟩)
            else (post.1 .normal actual).down) afterGuard⟩, ⟨⟩)) :
    Std.Do.Triple (m := StateT (State Γ) Part) (ps := .arg (State Γ) .pure)
      ((Stmt.while guard body).action program) (fun entry => ⟨invariant entry⟩) post := by
  have sourceStep : ∀ start, invariant start →
      TotalWP program guard (fun _ => False)
        (fun again afterGuard =>
          if again then
            TotalWP program body (fun next => invariant next ∧ relation next start)
              (fun value finish => (post.1 (.returned value) finish).down) afterGuard
          else (post.1 .normal afterGuard).down) start := by
    intro start initial
    exact (TotalWP.iff_triple_action.mpr (step start initial)).mono_post
      (fun _ impossible => impossible) (by
        intro again afterGuard property
        cases again with
        | false => exact property
        | true => exact TotalWP.iff_triple_action.mpr property)
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro entry initial
  obtain ⟨finish, control, execution, property⟩ :=
    TotalWP.while_wellFounded wellFounded sourceStep initial
  refine ⟨(control, finish), mem_action_iff.mpr execution, ?_⟩
  cases control with
  | normal => exact property
  | returned value => exact property
  | fault error => exact False.elim property

end Complexity.Language.Stmt
