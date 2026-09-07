/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Complexity

/-!
# Problem-owned specifications and submission certificates

A track publishes one `Problem` and a requested bound. A submission supplies
only code and a proof for those *fixed* parameters. In particular, input
encoding, legal word widths, the size measure, and the observable answer are
not fields of the submission.

This is a specification boundary, not a security mechanism: the problem author
still has to choose an honest encoding and size measure. The general judgments
in `Ram.Complexity` remain useful without these packaging conventions.

Concrete budgets work for finite and infinite domains alike. The asymptotic
track additionally requires legal inputs of arbitrarily large size, so a
threshold cannot discard its entire domain.
-/

namespace Ram

/-- All problem-specific choices are published before accepting submissions.
`encode` is external input formatting, not computation charged to the program;
it must not perform the work that the problem asks the program to do. -/
structure Problem (Input : Type) where
  encode : ∀ w, Input → List (Word w)
  admissible : Nat → Input → Prop
  size : Input → Nat
  post : ∀ w, Input → State w → Prop

namespace Problem

/-- The legal input family contains arbitrarily large problem sizes. Word
width may grow with the input; one fixed finite width is usually insufficient. -/
def Unbounded (p : Problem Input) : Prop :=
  ∀ n, ∃ w input, p.admissible w input ∧ n ≤ p.size input

theorem Unbounded.nonempty {p : Problem Input} (h : p.Unbounded) :
    ∃ w input, p.admissible w input := by
  obtain ⟨w, input, ha, _⟩ := h 0
  exact ⟨w, input, ha⟩

/-- A size-bounded problem is perfectly suitable for concrete budgets, but
cannot be presented as an unbounded asymptotic problem. -/
theorem not_unbounded_of_bounded {p : Problem Input} {limit : Nat}
    (h : ∀ w input, p.admissible w input → p.size input ≤ limit) :
    ¬ p.Unbounded := by
  intro hu
  obtain ⟨w, input, ha, hs⟩ := hu (limit + 1)
  have := h w input ha
  omega

end Problem

/-- Only code is chosen by a submission; `p` is the already published problem.
The expected type at the acceptance site must use that specific `p`. -/
structure Submission (p : Problem Input) where
  code : Code

namespace Submission

def Correct {p : Problem Input} (s : Submission p) : Prop :=
  UniformCorrect s.code p.encode p.admissible p.post

def Within {p : Problem Input} (s : Submission p) (bound : Nat → Nat) : Prop :=
  UniformTimeBound s.code p.encode p.admissible p.size p.post bound

theorem Within.correct {p : Problem Input} {s : Submission p}
    {bound : Nat → Nat} (h : s.Within bound) : s.Correct :=
  UniformTimeBound.correct h

end Submission

/-- A concrete-budget submission, including termination and the answer on
every legal input. Both the problem and required budget are fixed parameters. -/
structure Certificate (p : Problem Input) (bound : Nat → Nat)
    extends Submission p where
  verified : toSubmission.Within bound

namespace Certificate

theorem correct (c : Certificate p bound) : c.toSubmission.Correct :=
  c.verified.correct

/-- The certificate exposes the same actual-machine judgment used by runners
and the compiler; there is no separate evaluator or source-level cost table. -/
theorem runs (c : Certificate p bound) (ha : p.admissible w input) :
    ∃ finish, TerminatesWithin c.code (bound (p.size input))
      (State.initial (p.encode w input)) finish ∧ p.post w input finish :=
  c.verified w input ha

def weaken (c : Certificate p a) (h : ∀ n, a n ≤ b n) : Certificate p b where
  code := c.code
  verified := UniformTimeBound.mono c.verified h

end Certificate

/-- An asymptotic task must establish that its legal size parameter really
tends to infinity somewhere, rather than using a finite benchmark domain. -/
structure AsymptoticProblem (Input : Type) extends Problem Input where
  unbounded : toProblem.Unbounded

/-- Total correctness holds even below the asymptotic threshold. The growing
legal input family is supplied by the problem, never by the submission. -/
structure AsymptoticCertificate (p : AsymptoticProblem Input) (growth : Nat → Nat)
    extends Submission p.toProblem where
  verified : UniformBigO code p.encode p.admissible p.size p.post growth

namespace AsymptoticCertificate

theorem correct (c : AsymptoticCertificate p growth) : c.toSubmission.Correct :=
  c.verified.correct

/-- Reuse a proved concrete bound without reproving functional correctness. -/
def ofBound {p : AsymptoticProblem Input}
    (c : Certificate p.toProblem bound) {constant threshold : Nat}
    (hc : 0 < constant)
    (hb : ∀ n, threshold ≤ n → bound n ≤ constant * growth n) :
    AsymptoticCertificate p growth where
  code := c.code
  verified := UniformTimeBound.bigO c.verified hc hb

/-- Use mathlib's asymptotic analysis of a proved machine bound directly. -/
def ofIsBigO {Input : Type} {p : AsymptoticProblem Input}
    {bound growth : Nat → Nat} (c : Certificate p.toProblem bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    AsymptoticCertificate p growth where
  code := c.code
  verified := c.verified.bigO_of_isBigO hO

@[simp] theorem ofIsBigO_code {Input : Type} {p : AsymptoticProblem Input}
    {bound growth : Nat → Nat} (c : Certificate p.toProblem bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    (ofIsBigO c hO).code = c.code := rfl

end AsymptoticCertificate

/-- Even the halt instruction costs one transition from the initial running
state. This lower bound is independent of the problem's postcondition. -/
theorem TerminatesWithin.initial_pos {code : Code} {bound : Nat}
    {input : List (Word w)} {finish : State w}
    (h : TerminatesWithin code bound (State.initial input) finish) : 0 < bound := by
  obtain ⟨n, hn, he, hh⟩ := h
  have hpos : 0 < n := by
    cases n with
    | zero =>
      have hs := Exec.zero_iff.mp he
      rw [← hs] at hh
      cases hh
    | succ n => exact Nat.zero_lt_succ n
  omega

/-- On a genuinely unbounded legal domain, `O(0)` cannot be certified by
choosing a threshold beyond all inputs: some legal input crosses every one. -/
theorem AsymptoticProblem.not_bigO_zero (p : AsymptoticProblem Input) (code : Code) :
    ¬ UniformBigO code p.encode p.admissible p.size p.post (fun _ => 0) := by
  intro hO
  obtain ⟨_, constant, threshold, _, h⟩ := uniformBigO_iff_eventual.mp hO
  obtain ⟨w, input, ha, hs⟩ := p.unbounded threshold
  obtain ⟨finish, hr, _⟩ := h w input ha hs
  have hp := hr.initial_pos
  simp at hp

theorem AsymptoticCertificate.no_zero (c : AsymptoticCertificate p (fun _ => 0)) :
    False :=
  p.not_bigO_zero c.code c.verified

end Ram
