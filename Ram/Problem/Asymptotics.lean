/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Problem
import Ram.Complexity.Multivariate

/-!
# Published asymptotic bounds on a full input family

The problem, legal-input filter and growth expression are fixed parameters of
`AsymptoticCertificateAt`. A submission still supplies only one code list and
its proof; it cannot choose a different encoding, admissible domain or growth
regime. The filter must be nontrivial. Correctness covers every legal input,
including those outside the eventual asymptotic bound.

This extends the existing certificate interface without a second problem
definition or a new mathematical asymptotic relation. Scalar certificates and
concrete bounds reuse their exact programs and execution proofs.
-/

namespace Ram

/-- The existing problem-owned unboundedness witness supplies the nontrivial
filter required by a scalar or joint-size asymptotic certificate. -/
theorem Problem.Unbounded.neBot {p : Problem Input} (h : p.Unbounded) :
    (inputSizeFilter p.admissible p.size).NeBot :=
  inputSizeFilter_neBot_iff.mpr h

/-- A verified submission for a fixed full-input growth expression and a
fixed nontrivial legal-input regime. All-input correctness remains mandatory. -/
structure AsymptoticCertificateAt (p : Problem Input)
    (l : Filter (LegalInput p.admissible)) (growth : LegalInput p.admissible → Nat)
    [l.NeBot] extends Submission p where
  verified : UniformBigOAt code p.encode p.admissible p.post l growth

namespace AsymptoticCertificateAt

variable {p : Problem Input} {l : Filter (LegalInput p.admissible)} [l.NeBot]
variable {growth growth' : LegalInput p.admissible → Nat}

/-- The asymptotic regime never removes an input from functional correctness. -/
theorem correct (c : AsymptoticCertificateAt p l growth) : c.toSubmission.Correct :=
  c.verified.correct

/-- Analyze an existing concrete certificate on the full input family,
retaining its fixed code, encoding, admissibility and answer specification. -/
def ofIsBigO {bound : Nat → Nat} (c : Certificate p bound)
    (hO : Asymptotics.IsBigO l (fun i => (bound (p.size i.val.2) : ℝ))
      (fun i => (growth i : ℝ))) : AsymptoticCertificateAt p l growth where
  code := c.code
  verified := c.verified.bigOAt_of_isBigO hO

@[simp] theorem ofIsBigO_code {bound : Nat → Nat} (c : Certificate p bound)
    (hO : Asymptotics.IsBigO l (fun i => (bound (p.size i.val.2) : ℝ))
      (fun i => (growth i : ℝ))) : (ofIsBigO c hO).code = c.code := rfl

/-- Weaken only the requested asymptotic bound on the same regime. -/
def weaken (c : AsymptoticCertificateAt p l growth)
    (hO : Asymptotics.IsBigO l (fun i => (growth i : ℝ))
      (fun i => (growth' i : ℝ))) : AsymptoticCertificateAt p l growth' where
  code := c.code
  verified := c.verified.of_isBigO hO

/-- Restrict the growth regime without shrinking the problem's legal domain
or its all-input correctness proof. The new regime must remain nontrivial. -/
def restrict (c : AsymptoticCertificateAt p l growth)
    {l' : Filter (LegalInput p.admissible)} [l'.NeBot] (hle : l' ≤ l) :
    AsymptoticCertificateAt p l' growth where
  code := c.code
  verified := c.verified.filter_mono hle

/-- A halted run from the initial running state costs at least one transition,
so a nontrivial asymptotic regime cannot certify an identically zero bound. -/
theorem no_zero (c : AsymptoticCertificateAt p l (fun _ => 0)) : False := by
  obtain ⟨_, constant, _, h⟩ := uniformBigOAt_iff_eventual.mp c.verified
  obtain ⟨i, finish, hr, _⟩ := h.exists
  have hp := hr.initial_pos
  simp at hp

end AsymptoticCertificateAt

/-- A scalar certificate is already a full-input certificate. Its existing
problem supplies nontriviality, and the runtime proof is reused definitionally. -/
def AsymptoticCertificate.toAt {p : AsymptoticProblem Input} {growth : Nat → Nat}
    (c : AsymptoticCertificate p growth) :
    @AsymptoticCertificateAt Input p.toProblem (inputSizeFilter p.admissible p.size)
      (fun i => growth (p.size i.val.2)) p.unbounded.neBot := by
  letI := p.unbounded.neBot
  exact { code := c.code, verified := c.verified }

end Ram
