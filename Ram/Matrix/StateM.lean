/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Matrix.Frame
import Ram.Memory.StateM
import Ram.Verification.StateMModel

/-!
# Native stateful specifications for matrix entries

The abstract state is mathlib's ordinary matrix, and its operations are native
`StateM` observation and modification. A read transports the existing indexed
refinement through `Equiv.curry`; a store reuses the indexed implementation and
the proved matrix update rule. No new machine operation or cost annotation is
introduced. In particular, updating one row entry is still one existing source
store, not a constant-time whole-row update.

The predicates retain the complete concrete entry and endpoint, source heap
safety, and the matrix's non-wrapping row-major layout. Store injectivity is
derived from that layout bound, not imposed as an additional client premise.
-/

namespace Ram.Source.Matrix

variable {heapLimit depth : Nat} {program : Program} {base : Word w}

/-- Reading an entry is ordinary native state observation. Mathlib's curry
equivalence changes only the mathematical coordinates, not the RAM layout. -/
theorem read_stateM (entry : State w) (i : Fin m) (j : Fin n)
    (dst : Reg) (address : Expr) :
    Refines program heapLimit depth (.assign dst (.load address))
      (fun A s => s = entry ∧ MatrixAt heapLimit base A s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = matrixAddr base i j)
      (fun result finish => finish = entry.setReg dst result.1 ∧
        MatrixAt heapLimit base result.2 finish)
      ((do
        let A ← get
        pure (A i j)) : StateM (Matrix (Fin m) (Fin n) (Word w)) (Word w)).run := by
  have transported :=
    (Indexed.read_stateM (program := program) (heapLimit := heapLimit) (depth := depth)
      (layout := Function.uncurry (matrixAddr base : Fin m → Fin n → Word w))
      entry (i, j) dst address).stateM_equiv
        (Equiv.curry (Fin m) (Fin n) (Word w)) (Equiv.refl (Word w))
  rintro A s ⟨same, represented, reads, addressEq⟩
  subst s
  apply Verification.TotalWP.of_contract (transported A)
  · exact ⟨rfl, represented.indexed, reads, addressEq⟩
  · rintro finish ⟨endpoint, _⟩
    refine ⟨endpoint, ?_⟩
    rw [endpoint]
    exact represented.setReg dst (A i j)

/-- One source store refines native modification by the existing mathlib
row-update and function-update APIs. The exact endpoint and heap frame remain
available for composing later operations or retaining unrelated objects. -/
theorem store_stateM (entry : State w) (i : Fin m) (j : Fin n)
    (address value : Expr) (stored : Word w) :
    Refines program heapLimit depth (.store address value)
      (fun A s => s = entry ∧ MatrixAt heapLimit base A s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧
        value.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = matrixAddr base i j ∧ s.eval value = stored)
      (fun result finish => finish = entry.setMem (matrixAddr base i j) stored ∧
        MatrixAt heapLimit base result.2 finish ∧
        Set.EqOn finish.mem entry.mem ({matrixAddr base i j} : Set (Word w))ᶜ)
      (modify (fun A : Matrix (Fin m) (Fin n) (Word w) =>
        A.updateRow i (Function.update (A i) j stored)) :
        StateM (Matrix (Fin m) (Fin n) (Word w)) PUnit).run := by
  rintro A s ⟨same, represented, addressReads, valueReads, addressEq, valueEq⟩
  subst s
  apply Verification.TotalWP.of_contract
    (Indexed.store_stateM (program := program) (heapLimit := heapLimit) (depth := depth)
      (layout := Function.uncurry (matrixAddr base : Fin m → Fin n → Word w)) entry
      (matrixAddr_injective represented.1.fits) (i, j) address value stored
      (Function.uncurry A))
  · exact ⟨rfl, represented.indexed, addressReads, valueReads, addressEq, valueEq⟩
  · rintro finish ⟨endpoint, _, frame⟩
    refine ⟨endpoint, ?_, frame⟩
    rw [endpoint]
    exact represented.setMem i j stored

/-- The same implementation can use mathlib's column-update coordinates.
Only the represented mathematical result changes; the already-proved store
execution and its singleton-complement frame are reused unchanged. -/
theorem store_col_stateM (entry : State w) (i : Fin m) (j : Fin n)
    (address value : Expr) (stored : Word w) :
    Refines program heapLimit depth (.store address value)
      (fun A s => s = entry ∧ MatrixAt heapLimit base A s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧
        value.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = matrixAddr base i j ∧ s.eval value = stored)
      (fun result finish => finish = entry.setMem (matrixAddr base i j) stored ∧
        MatrixAt heapLimit base result.2 finish ∧
        Set.EqOn finish.mem entry.mem ({matrixAddr base i j} : Set (Word w))ᶜ)
      (modify (fun A : Matrix (Fin m) (Fin n) (Word w) =>
        A.updateCol j (Function.update (fun r => A r j) i stored)) :
        StateM (Matrix (Fin m) (Fin n) (Word w)) PUnit).run := by
  refine (store_stateM (program := program) (heapLimit := heapLimit) (depth := depth)
    (base := base) entry i j address value stored).congr_fun ?_
  intro A
  simp only [StateT.run_modify, _root_.Matrix.updateCol_update]

end Ram.Source.Matrix
