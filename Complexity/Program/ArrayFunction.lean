/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Input

/-!
# Compatibility with the single-array source interface

`Language.ArrayFunction.toProgram` selects the same source function under the
fixed `Program (Array Nat) Nat` interface. It retains the existing preloaded
array, argument environment and exact natural result. The return and correctness
equivalences reuse the existing evaluator; they add neither a wrapper body nor
an input conversion, and require no machine or resource assumptions.
-/

namespace Complexity.Language.ArrayFunction

/-- Present an existing array function through the fixed typed interface,
retaining its source table, selected body and canonical preloaded input. -/
def toProgram (f : ArrayFunction) : Complexity.Program (Array Nat) Nat where
  signatures := f.signatures
  source := f.program
  fn := f.fn
  signature := congrArg₂ Signature.mk f.parameterTypes f.resultType

/-- Both interfaces pass exactly the same source argument environment. -/
@[simp] theorem toProgram_args (f : ArrayFunction) (xs : Array Nat) :
    f.toProgram.args xs = f.args xs := rfl

private theorem nat_result_cast_rel {τ : Ty} (same : τ = .nat)
    (result : Nat) (value : Value τ) (heap : Heap) :
    (cast (congrArg (Representation Nat) same.symm) Representation.nat).Rel result value heap ↔
      (Equiv.cast (congrArg Value same)) value = result := by
  cases same
  change result = value ↔ value = result
  exact eq_comm

/-- The typed output observation is the original exact natural result, with
only its source type transported. The final heap is not changed. -/
@[simp] theorem toProgram_resultRepresentation_rel (f : ArrayFunction)
    (result : Nat) (value : Value f.signatures[f.fn].result) (heap : Heap) :
    f.toProgram.resultRepresentation.Rel result value heap ↔ f.resultEquiv value = result :=
  nat_result_cast_rel f.resultType result value heap

/-- Returning a mathematical natural is the same successful source execution
under either interface. -/
@[simp] theorem toProgram_returns_iff (f : ArrayFunction) (xs : Array Nat) (result : Nat) :
    f.toProgram.Returns xs result ↔ f.Returns xs result := by
  constructor
  · rintro ⟨value, heap, evaluated, represented⟩
    have same := (toProgram_resultRepresentation_rel f result value heap).mp represented
    have returned : value = f.resultEquiv.symm result := by
      apply f.resultEquiv.injective
      simpa only [Equiv.apply_symm_apply] using same
    refine ⟨heap, ?_⟩
    rw [← returned]
    exact evaluated
  · rintro ⟨heap, evaluated⟩
    refine ⟨f.resultEquiv.symm result, heap, evaluated, ?_⟩
    exact (toProgram_resultRepresentation_rel f result (f.resultEquiv.symm result) heap).mpr
      (f.resultEquiv.apply_symm_apply result)

/-- Existing array correctness proofs transfer directly to the equality
instance of the typed mathematical postcondition, with the same legal inputs. -/
@[simp] theorem toProgram_correct_iff (f : ArrayFunction) (valid : Array Nat → Prop)
    (answer : Array Nat → Nat) :
    f.toProgram.Correct valid (fun xs result => result = answer xs) ↔ f.Correct valid answer := by
  constructor
  · intro correct xs legal
    obtain ⟨result, returned, same⟩ := correct xs legal
    exact (toProgram_returns_iff f xs (answer xs)).mp (same ▸ returned)
  · intro correct xs legal
    exact ⟨answer xs, (toProgram_returns_iff f xs (answer xs)).mpr (correct xs legal), rfl⟩

end Complexity.Language.ArrayFunction
