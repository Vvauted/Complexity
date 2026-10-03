/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Problem.Basic
import Complexity.Computability.Ram.Space.Basic

/-!
# Problem-owned RAM space certificates

The problem fixes encoding, legal widths, size and answer before a submission
chooses code. Space counts the cumulative distinct physical heap words in the
same successful execution that establishes the answer. Raw encoded input lives
in the RAM input stream, not in preloaded heap cells. An asymptotic certificate
still proves total correctness on every legal input.
-/

namespace Ram

namespace Submission

/-- A concrete bound on the physical heap words used by this submission. -/
def SpaceWithin {p : Problem Input} (s : Submission p)
    (bound : Nat → Nat) : Prop :=
  UniformSpaceBound s.code p.encode p.admissible p.size p.post bound

theorem SpaceWithin.correct {p : Problem Input} {s : Submission p}
    {bound : Nat → Nat} (h : s.SpaceWithin bound) : s.Correct :=
  UniformSpaceBound.correct h

end Submission

/-- A concrete space-budget certificate for one fixed problem and code. -/
structure SpaceCertificate (p : Problem Input) (bound : Nat → Nat)
    extends Submission p where
  verified : toSubmission.SpaceWithin bound

namespace SpaceCertificate

theorem correct (c : SpaceCertificate p bound) : c.toSubmission.Correct :=
  c.verified.correct

/-- Expose one exact halted execution, answer and physical-word bound. -/
theorem runs (c : SpaceCertificate p bound) (legal : p.admissible w input) :
    ∃ steps finish,
      SpaceBound c.code steps (State.initial (p.encode w input)) finish ∅
        (bound (p.size input)) ∧ p.post w input finish :=
  c.verified w input legal

def weaken (c : SpaceCertificate p a) (h : ∀ n, a n ≤ b n) :
    SpaceCertificate p b where
  code := c.code
  verified := UniformSpaceBound.mono c.verified h

/-- Combine independent time and space proofs of the same code by uniqueness
of the halted RAM run; the returned answer belongs to that very run. -/
theorem with_time (space : SpaceCertificate p spaceBound)
    (time : Certificate p timeBound) (sameCode : time.code = space.code)
    (legal : p.admissible w input) :
    ∃ steps finish,
      Exec space.code steps (State.initial (p.encode w input)) finish ∧
      finish.status = .halted ∧ p.post w input finish ∧
      steps ≤ timeBound (p.size input) ∧
      spaceWords space.code steps (State.initial (p.encode w input)) ∅ ≤
        spaceBound (p.size input) := by
  have timeVerified : UniformTimeBound space.code p.encode p.admissible p.size p.post
      timeBound := by
    have original : UniformTimeBound time.code p.encode p.admissible p.size p.post
        timeBound := time.verified
    simpa only [sameCode] using original
  exact UniformSpaceBound.with_time timeVerified space.verified legal

end SpaceCertificate

/-- A scalar asymptotic space claim on an unbounded problem-owned family. -/
structure AsymptoticSpaceCertificate (p : AsymptoticProblem Input)
    (growth : Nat → Nat) extends Submission p.toProblem where
  verified : UniformSpaceBigO code p.encode p.admissible p.size p.post growth

namespace AsymptoticSpaceCertificate

theorem correct (c : AsymptoticSpaceCertificate p growth) :
    c.toSubmission.Correct :=
  c.verified.correct

/-- Reuse the exact code and runs of a concrete certificate; only the
mathematical asymptotic analysis is new. -/
def ofIsBigO {p : AsymptoticProblem Input} {bound growth : Nat → Nat}
    (c : SpaceCertificate p.toProblem bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    AsymptoticSpaceCertificate p growth where
  code := c.code
  verified := c.verified.bigO_of_isBigO hO

@[simp] theorem ofIsBigO_code {p : AsymptoticProblem Input}
    {bound growth : Nat → Nat} (c : SpaceCertificate p.toProblem bound)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun n => (bound n : ℝ)) (fun n => (growth n : ℝ))) :
    (ofIsBigO c hO).code = c.code := rfl

end AsymptoticSpaceCertificate

end Ram
