/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Component.Realization
import Complexity.Computability.Ram.Problem.Asymptotics

/-!
# Input-dependent bounds for an existing component

`TimeBoundOn` refines the actual body cost of one already fixed component.
It may retain several input parameters rather than compressing them into the
component's scalar resource envelope. Code, domains, representations, heap
capacity and depth requirements are unchanged.

Composition uses the first cost at `x` and the second at the actual `f x`.
Both components run on their shared intermediate representation, and call
relocation uses the existing linking theorems. No representation conversion
or abstract computation is inserted into the machine program.
-/

namespace Ram.Component

universe u v z

variable {α : Type u} {β : Type v} {γ : Type z}
variable {A : Interface α} {B : Interface β} {C : Interface γ}
variable {f : α → β} {g : β → γ} {D : Nat → α → Prop} {E : Nat → β → Prop}

/-- A refined input-dependent time bound on the same measured body execution.
The existing component still fixes every non-time resource requirement. -/
def TimeBoundOn (p : Component A B f D) (time : Nat → α → Nat) : Prop :=
  ∀ {w} x, D w x → ∀ s, A.represents w x s →
    ∀ heapLimit depth, p.heapBound (A.size x) ≤ heapLimit →
      p.depthBound (A.size x) ≤ depth →
      ∃ steps t,
        Source.LocalMeasuredExec p.locals p.functions heapLimit depth p.body steps s t ∧
        B.represents w (f x) t ∧ steps ≤ time w x

/-- Every component already has its original scalar time bound on all inputs. -/
theorem timeBoundOn (p : Component A B f D) :
    p.TimeBoundOn (fun _ x => p.timeBound (A.size x)) := p.correct

/-- Erasing the pre-existing time envelope gives exactly the independent
conditional bound on the same program, not a different execution notion. -/
theorem timeBoundOn_iff_toTotalComponent (p : Component A B f D) (time : Nat → α → Nat) :
    p.TimeBoundOn time ↔ p.toTotalComponent.TimeBoundOn time := by
  constructor
  · intro h w x hx H d hH hd s hs steps t execution
    obtain ⟨count, finish, measured, _, bound⟩ := h x hx s hs H d hH hd
    exact (measured.deterministic execution).1 ▸ bound
  · intro h w x hx s hs H d hH hd
    exact h.contract x hx hH hd s hs

namespace TimeBoundOn

variable {p : Component A B f D} {time time' : Nat → α → Nat}

/-- Increase the refined budget only where the component's domain holds. -/
theorem mono (h : p.TimeBoundOn time)
    (hle : ∀ w x, D w x → time w x ≤ time' w x) : p.TimeBoundOn time' := by
  intro w x hx s hs H d hH hd
  obtain ⟨steps, t, he, ht, hb⟩ := h x hx s hs H d hH hd
  exact ⟨steps, t, he, ht, hb.trans (hle w x hx)⟩

/-- Refined time adds at the actual intermediate value. The component's
existing capacity and depth envelopes are still used to justify both runs. -/
theorem comp {q : Component B C g E} {secondTime : Nat → β → Nat}
    (second : q.TimeBoundOn secondTime) (first : p.TimeBoundOn time)
    (hdom : ∀ w x, D w x → E w (f x)) :
    (q.comp p hdom).TimeBoundOn (fun w x => time w x + secondTime w (f x)) := by
  intro w x hx s hs H d hH hd
  obtain ⟨np, middle, hp, hm, hnp⟩ := first x hx s hs H d
    ((Nat.le_max_left _ _).trans hH) ((Nat.le_max_left _ _).trans hd)
  have hsize := p.size_le w x hx
  have hhq : q.heapBound (B.size (f x)) ≤ H :=
    (Asymptotics.le_monotoneHull _ _).trans ((Asymptotics.hull_monotone _ hsize).trans
      ((Nat.le_max_right _ _).trans hH))
  have hdq : q.depthBound (B.size (f x)) ≤ d :=
    (Asymptotics.le_monotoneHull _ _).trans ((Asymptotics.hull_monotone _ hsize).trans
      ((Nat.le_max_right _ _).trans hd))
  obtain ⟨nq, t, hq, ht, hnq⟩ := second (f x) (hdom w x hx) middle hm H d hhq hdq
  have hp' := hp.renameCalls_rebase (Program.embeds_link_left p.functions q.functions)
    (max p.locals q.locals)
  have hq' := hq.renameCalls_rebase (Program.embeds_link_right p.functions q.functions)
    (max p.locals q.locals)
  rw [Stmt.renameCalls_id] at hp'
  exact ⟨np + nq, t, .seq hp' hq', ht, Nat.add_le_add hnp hnq⟩

/-- The refined bound reaches the same complete compiled machine, including
one header read and one halt, with the existing capacity and input premises. -/
theorem runs_observed (h : p.TimeBoundOn time) {w : Nat} (x : α)
    (hx : D w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w) (hcapacity : p.capacity (A.size x) < 2 ^ w) :
    ∃ sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧
      TerminatesWithin p.code (time w x + 2)
        (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
      Source.State.Observes (p.heapBound (A.size x)) p.locals sourceFinal targetFinal := by
  have contract : Source.Contract p.locals p.functions (p.heapBound (A.size x))
      (p.depthBound (A.size x)) p.body (A.represents w x) (B.represents w (f x))
      (fun _ => time w x) :=
    fun s hs => h x hx s hs _ _ le_rfl le_rfl
  exact contract.compile_observed p.compile_eq hcode hcapacity hinput

end TimeBoundOn

namespace Realization

variable {α : Type} {A : Interface α} {f : α → β} {D : Nat → α → Prop}
variable {p : Component A B f D} {problem : Problem α} {time : Nat → α → Nat}

/-- A refined component bound runs on every input of the same published
problem. The existing realization supplies all encoding and capacity facts. -/
theorem runs_timeBoundOn (r : Realization p problem) (h : p.TimeBoundOn time)
    {w : Nat} {x : α} (hx : problem.admissible w x) :
    ∃ t, TerminatesWithin p.code (time w x + 2)
      (State.initial (problem.encode w x)) t ∧ problem.post w x t := by
  obtain ⟨s, t, hr, he, ho⟩ := h.runs_observed x (r.domain_of_admissible w x hx)
    (r.input w x) (r.represents_input w x hx) (r.code_fits w x hx)
    (r.capacity_fits w x hx)
  exact ⟨t, by simpa only [r.encode_eq] using he, r.post_of_observes w x hx s t hr ho⟩

/-- Export refined input-dependent time to a fixed multivariate asymptotic
certificate. Neither the code nor the legal problem domain changes. -/
def toAsymptoticCertificateAt (r : Realization p problem) (h : p.TimeBoundOn time)
    {l : Filter (LegalInput problem.admissible)} [l.NeBot]
    {growth : LegalInput problem.admissible → Nat}
    (hO : Asymptotics.IsBigO l (fun i => ((time i.val.1 i.val.2 + 2 : Nat) : ℝ))
      (fun i => (growth i : ℝ))) : AsymptoticCertificateAt problem l growth where
  code := p.code
  verified := UniformBigOAt.of_terminatesWithin
    (fun i => r.runs_timeBoundOn h i.property) hO

@[simp] theorem toAsymptoticCertificateAt_code (r : Realization p problem)
    (h : p.TimeBoundOn time) {l : Filter (LegalInput problem.admissible)} [l.NeBot]
    {growth : LegalInput problem.admissible → Nat}
    (hO : Asymptotics.IsBigO l (fun i => ((time i.val.1 i.val.2 + 2 : Nat) : ℝ))
      (fun i => (growth i : ℝ))) : (r.toAsymptoticCertificateAt h hO).code = p.code := rfl

end Realization
end Ram.Component
