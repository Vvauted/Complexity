import Ram.Problem
import Ram.Examples.Arithmetic

/-!
# One fixed multiplication task, not a submitter-chosen encoding

The published input is exactly the two operands. The expected output is their
natural-number product, and the legal-width predicate ensures it fits. The
same seven-instruction program works at every legal width.

The declared size is the maximum *numeric value* of the operands. Constant
word-RAM time here is not a bit-complexity claim: a word multiplication is one
instruction in this machine model, at every width.
-/

namespace Ram.Examples

def multiplicationProblem : AsymptoticProblem (Nat × Nat) where
  encode w input := [BitVec.ofNat w input.1, BitVec.ofNat w input.2]
  admissible w input :=
    input.1 < 2 ^ w ∧ input.2 < 2 ^ w ∧ input.1 * input.2 < 2 ^ w
  size input := max input.1 input.2
  post _ input finish := finish.output.map BitVec.toNat = [input.1 * input.2]
  unbounded := by
    intro n
    refine ⟨n, (n, 0), ?_, ?_⟩
    · exact ⟨Nat.lt_two_pow_self, Nat.two_pow_pos n,
        by simpa only [Nat.mul_zero] using Nat.two_pow_pos n⟩
    · simp

/-- A track can request this type directly. Neither encoding nor the expected
answer can be replaced by fields of the supplied certificate. -/
def multiplicationCertificate :
    Certificate multiplicationProblem.toProblem (fun _ => 7) where
  code := multiply
  verified := by
    intro w input ha
    exact multiply_exact ha.1 ha.2.1 ha.2.2

def multiplicationConstantTime :
    AsymptoticCertificate multiplicationProblem (fun _ => 1) :=
  .ofBound multiplicationCertificate (constant := 7) (threshold := 0)
    (by decide) (by intro n _; simp)

/-- A bounded contest domain is also supported, but with an explicit concrete
budget instead of pretending that finitely many legal sizes tend to infinity. -/
def boundedMultiplicationProblem (limit : Nat) : Problem (Nat × Nat) :=
  { multiplicationProblem.toProblem with
    admissible := fun w input => multiplicationProblem.admissible w input ∧
      multiplicationProblem.size input ≤ limit }

def boundedMultiplicationCertificate (limit : Nat) :
    Certificate (boundedMultiplicationProblem limit) (fun _ => 7) where
  code := multiply
  verified := by
    intro w input ha
    exact multiplicationCertificate.verified w input ha.1

theorem boundedMultiplication_not_unbounded (limit : Nat) :
    ¬ (boundedMultiplicationProblem limit).Unbounded := by
  apply Problem.not_unbounded_of_bounded (limit := limit)
  intro w input ha
  exact ha.2

end Ram.Examples
