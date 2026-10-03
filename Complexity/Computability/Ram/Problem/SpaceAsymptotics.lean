/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Problem.Space
import Complexity.Computability.Ram.Problem.Asymptotics
import Complexity.Computability.Ram.Space.Multivariate

/-!
# Problem-owned full-input asymptotic RAM space bounds

The task fixes one problem, legal-input filter and growth expression. A
submission provides one code list and a proof about its actual cumulative
physical-word footprint. The filter must be nontrivial, while correctness
still covers all legal inputs, including those below the asymptotic threshold.
Zero space is possible for a RAM program that never accesses heap memory.
-/

namespace Ram

/-- Space complexity on a fixed nontrivial legal-input regime. -/
structure AsymptoticSpaceCertificateAt (p : Problem Input)
    (l : Filter (LegalInput p.admissible))
    (growth : LegalInput p.admissible → Nat)
    [l.NeBot] extends Submission p where
  verified : UniformSpaceBigOAt code p.encode p.admissible p.post l growth

namespace AsymptoticSpaceCertificateAt

variable {p : Problem Input} {l : Filter (LegalInput p.admissible)} [l.NeBot]
variable {growth growth' : LegalInput p.admissible → Nat}

theorem correct (c : AsymptoticSpaceCertificateAt p l growth) :
    c.toSubmission.Correct :=
  c.verified.correct

/-- Analyze an already proved concrete physical-word budget on this full
input family, without changing the program or its executions. -/
def ofIsBigO {bound : Nat → Nat} (c : SpaceCertificate p bound)
    (hO : Asymptotics.IsBigO l (fun i => (bound (p.size i.val.2) : ℝ))
      (fun i => (growth i : ℝ))) :
    AsymptoticSpaceCertificateAt p l growth where
  code := c.code
  verified := c.verified.bigOAt_of_isBigO hO

@[simp] theorem ofIsBigO_code {bound : Nat → Nat} (c : SpaceCertificate p bound)
    (hO : Asymptotics.IsBigO l (fun i => (bound (p.size i.val.2) : ℝ))
      (fun i => (growth i : ℝ))) :
    (ofIsBigO c hO).code = c.code := rfl

/-- Weaken the target while retaining the same legal family and exact run. -/
def weaken (c : AsymptoticSpaceCertificateAt p l growth)
    (hO : Asymptotics.IsBigO l (fun i => (growth i : ℝ))
      (fun i => (growth' i : ℝ))) :
    AsymptoticSpaceCertificateAt p l growth' where
  code := c.code
  verified := c.verified.of_isBigO hO

/-- Restrict only the asymptotic regime, not the all-input correctness claim. -/
def restrict (c : AsymptoticSpaceCertificateAt p l growth)
    {l' : Filter (LegalInput p.admissible)} [l'.NeBot] (hle : l' ≤ l) :
    AsymptoticSpaceCertificateAt p l' growth where
  code := c.code
  verified := c.verified.filter_mono hle

end AsymptoticSpaceCertificateAt

/-- A scalar space certificate is definitionally a full-input certificate on
the problem's existing unbounded legal-size filter. -/
def AsymptoticSpaceCertificate.toAt {p : AsymptoticProblem Input}
    {growth : Nat → Nat} (c : AsymptoticSpaceCertificate p growth) :
    @AsymptoticSpaceCertificateAt Input p.toProblem
      (inputSizeFilter p.admissible p.size)
      (fun i => growth (p.size i.val.2)) p.unbounded.neBot := by
  letI := p.unbounded.neBot
  exact { code := c.code, verified := c.verified }

end Ram
