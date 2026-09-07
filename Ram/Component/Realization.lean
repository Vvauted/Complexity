/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Component.Composition

/-!
# Realizing a component on a fixed problem

A component is a conditional reusable contract. By itself, it does not assert
that every abstract input is representable or that the compiled program fits
every word width. `Component.Realization` supplies these facts for every input
of a previously fixed `Problem`, along with the actual input encoding and
observable answer. It never shrinks the problem's domain.

## Main results

- `Component.Realization.toCertificate`: a complete fixed-problem certificate.
- `Component.Realization.runs_polynomial`: unconditional-on-capacity polynomial
  execution for all inputs accepted by that problem.
- `Component.Realization.exists_asymptoticCertificate`: the corresponding
  certificate when the problem supplies an unbounded legal input family.
-/

namespace Ram.Component

universe v

variable {α : Type} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {domain : Nat → α → Prop}

/-- The connection between a reusable component and one published problem.
All input, capacity, and observation obligations cover the problem's full domain. -/
structure Realization (p : Component A B f domain) (problem : Problem α) where
  /-- Source input after the actual compiler-header read. -/
  input : ∀ w, α → List (Word w)
  /-- The component uses the size measure fixed by the problem. -/
  size_eq : problem.size = A.size
  /-- The actual published encoding contains this header and source input. -/
  encode_eq : ∀ w x, problem.encode w x =
    BitVec.ofNat w (p.heapBound (A.size x)) :: input w x
  /-- Every legal problem input satisfies the component's domain. -/
  domain_of_admissible : ∀ w x, problem.admissible w x → domain w x
  /-- Every legal input is represented in the actual zero-initialized start state. -/
  represents_input : ∀ w x, problem.admissible w x →
    A.represents w x (Source.State.initial (input w x))
  /-- The fixed compiled program fits every allowed word width. -/
  code_fits : ∀ w x, problem.admissible w x → p.code.length < 2 ^ w
  /-- The sufficient heap and stack capacity fits every allowed word width. -/
  capacity_fits : ∀ w x, problem.admissible w x → p.capacity (A.size x) < 2 ^ w
  /-- The represented result implies the published answer on the same machine state. -/
  post_of_observes : ∀ w x, problem.admissible w x → ∀ s t,
    B.represents w (f x) s →
    Source.State.Observes (p.heapBound (A.size x)) p.locals s t → problem.post w x t

namespace Realization

variable {p : Component A B f domain} {problem : Problem α}

/-- Produce a submission certificate without any additional runtime premises. -/
def toCertificate (r : Realization p problem) : Certificate problem p.totalTime :=
  p.certificate_observed problem r.input r.size_eq r.encode_eq r.domain_of_admissible
    r.represents_input r.code_fits r.capacity_fits r.post_of_observes

@[simp] theorem toCertificate_code (r : Realization p problem) :
    r.toCertificate.code = p.code := rfl

/-- Every input admitted by the fixed problem has a successful concrete run. -/
theorem runs (r : Realization p problem) {w : Nat} {x : α}
    (hx : problem.admissible w x) :
    ∃ t, TerminatesWithin p.code (p.totalTime (problem.size x))
      (State.initial (problem.encode w x)) t ∧ problem.post w x t :=
  r.toCertificate.runs hx

/-- Polynomial time on the entire published input family. Unlike a bare
component contract, this theorem needs only the published admissibility predicate. -/
theorem runs_polynomial (r : Realization p problem)
    (htime : IsPolynomiallyBounded p.timeBound) :
    ∃ c k : Nat, 0 < c ∧ ∀ (w : Nat) (x : α), problem.admissible w x →
      ∃ t, TerminatesWithin p.code (c * (problem.size x + 1) ^ k)
        (State.initial (problem.encode w x)) t ∧ problem.post w x t := by
  obtain ⟨c, k, hc, hb⟩ := (p.totalTime_polynomial htime).exists_pos
  refine ⟨c, k, hc, ?_⟩
  intro w x hx
  obtain ⟨t, he, hp⟩ := r.runs hx
  exact ⟨t, he.mono (hb _), hp⟩

/-- An unbounded legal problem family supports an asymptotic certificate.
The same fixed code still terminates correctly below every asymptotic threshold. -/
theorem exists_asymptoticCertificate {problem : AsymptoticProblem α}
    (r : Realization p problem.toProblem) (htime : IsPolynomiallyBounded p.timeBound) :
    ∃ k : Nat, Nonempty (AsymptoticCertificate problem (fun n => (n + 1) ^ k)) := by
  obtain ⟨c, k, hc, hb⟩ := (p.totalTime_polynomial htime).exists_pos
  exact ⟨k, ⟨AsymptoticCertificate.ofBound r.toCertificate (threshold := 0)
    hc (fun n _ => hb n)⟩⟩

end Realization
end Ram.Component
