/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Frame

/-!
# Budget-free read and store contracts for indexed models

Finite functions, matrix views and other indexed layouts share these contracts
for ordinary source loads and stores. Their mathematical contents are normal
functions; storing a word is the existing `Function.update`. Address evaluation
and heap access remain explicit safety premises, while representation lookup,
state updates and memory framing are proved here once.

The contracts apply directly with `ram_total_apply`; no model-specific weakest
precondition wrapper is needed. They specify the existing terminating safe
execution without selecting an instruction budget or adding a memory primitive.
-/

namespace Ram.Source.Indexed

/-- Read a represented cell into a source variable, preserving the entire
indexed model. The exact state equality also retains every other component. -/
theorem read_contract {ι : Type*} {heapLimit depth : Nat} {program : Program}
    {layout : ι → Word w} {values : ι → Word w}
    (i : ι) (dst : Reg) (address : Expr) :
    TotalRelContract program heapLimit depth (.assign dst (.load address))
      (fun s => IndexedAt heapLimit layout values s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧ s.eval address = layout i)
      (fun entry finish => finish = entry.setReg dst (values i) ∧
        IndexedAt heapLimit layout values finish) := by
  apply Verification.verify_total_rel
  intro entry ⟨represented, reads, addressEq⟩
  apply Verification.TotalWP.assign_iff.mpr
  refine ⟨⟨reads, ?_⟩, ?_⟩
  · change (entry.eval address).toNat < heapLimit
    rw [addressEq]
    exact represented.addr_lt i
  · have valueEq : entry.eval (.load address) = values i := by
      change entry.mem (entry.eval address) = values i
      rw [addressEq]
      exact represented.lookup i
    rw [valueEq]
    exact ⟨rfl, represented.setReg dst (values i)⟩

/-- Store a represented cell with standard function-update semantics. The
address layout must be injective, and both expressions must be safe to evaluate.
The standard singleton-complement frame is sufficient to preserve any disjoint
heap model through the existing whole-block frame rules. -/
theorem store_contract {ι : Type*} [DecidableEq ι] {heapLimit depth : Nat}
    {program : Program} {layout : ι → Word w} {values : ι → Word w}
    (hinj : Function.Injective layout) (i : ι) (address value : Expr) (stored : Word w) :
    TotalRelContract program heapLimit depth (.store address value)
      (fun s => IndexedAt heapLimit layout values s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧
        value.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = layout i ∧ s.eval value = stored)
      (fun entry finish => finish = entry.setMem (layout i) stored ∧
        IndexedAt heapLimit layout (Function.update values i stored) finish ∧
        Set.EqOn finish.mem entry.mem ({layout i} : Set (Word w))ᶜ) := by
  apply Verification.verify_total_rel
  intro entry ⟨represented, addressReads, valueReads, addressEq, valueEq⟩
  apply Verification.TotalWP.store_iff.mpr
  refine ⟨addressReads, valueReads, ?_, ?_⟩
  · rw [addressEq]
    exact represented.addr_lt i
  · rw [addressEq, valueEq]
    refine ⟨rfl, represented.setMem hinj i stored, ?_⟩
    intro a ha
    apply State.setMem_ne
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha

end Ram.Source.Indexed
