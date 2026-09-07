/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Memory.Finmap

/-!
# Ordinary store blocks implementing finite-map updates

These budget-free contracts connect fixed source statements to mathlib's
`Finmap.insert` and `Finmap.erase`. The represented key is ghost data appearing
only in the precondition and result, not in the program's syntax. Runtime
addresses and values are already in the specified registers, as required by
explicit preconditions; address calculation and table initialization are not
provided for free.

Insertion writes the payload before a nonzero presence marker. Both stores
read only registers, so changing memory cannot invalidate the second store's
operands. Erasure stores the ordinary source constant zero into the marker;
its compiled constant evaluation remains part of the existing machine cost.
The exact final state and standard `Set.EqOn` frames retain all other memory.
-/

namespace Ram.Source.Finmap

/-- Two ordinary register-addressed stores implement native finite-map
insertion, with no dependence of the program text on the represented key. -/
theorem insert_contract {κ : Type*} [DecidableEq κ] {heapLimit depth : Nat}
    {program : Program} {layout : κ × Bool → Word w}
    {map : Finmap (fun _ : κ => Word w)}
    (key : κ) (value marker : Word w) (payloadReg valueReg flagReg markerReg : Reg) :
    TotalRelContract program heapLimit depth
      (.seq (.store (.var payloadReg) (.var valueReg))
        (.store (.var flagReg) (.var markerReg)))
      (fun s => FinmapAt heapLimit layout map s ∧ Function.Injective layout ∧
        marker ≠ 0 ∧ s.regs payloadReg = layout (key, true) ∧
        s.regs valueReg = value ∧ s.regs flagReg = layout (key, false) ∧
        s.regs markerReg = marker)
      (fun entry finish =>
        finish = (entry.setMem (layout (key, true)) value).setMem
          (layout (key, false)) marker ∧
        FinmapAt heapLimit layout (map.insert key value) finish ∧
        Set.EqOn finish.mem entry.mem
          ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ) := by
  apply Verification.verify_total_rel
  intro entry ⟨represented, injective, nonzero, payload, stored, flag, presence⟩
  apply Verification.TotalWP.seq_iff.mpr
  apply Verification.TotalWP.store_iff.mpr
  refine ⟨trivial, trivial, ?_, ?_⟩
  · change (entry.regs payloadReg).toNat < heapLimit
    rw [payload]
    exact represented.addr_lt (key, true)
  · have payloadEval : entry.eval (.var payloadReg) = layout (key, true) := payload
    have storedEval : entry.eval (.var valueReg) = value := stored
    rw [payloadEval, storedEval]
    apply Verification.TotalWP.store_iff.mpr
    refine ⟨trivial, trivial, ?_, ?_⟩
    · change (entry.regs flagReg).toNat < heapLimit
      rw [flag]
      exact represented.addr_lt (key, false)
    · have flagEval : (entry.setMem (layout (key, true)) value).eval (.var flagReg) =
          layout (key, false) := flag
      have markerEval : (entry.setMem (layout (key, true)) value).eval (.var markerReg) =
          marker := presence
      rw [flagEval, markerEval]
      refine ⟨rfl, represented.setMem_insert injective key value marker nonzero, ?_⟩
      intro a ha
      have outside : a ≠ layout (key, true) ∧ a ≠ layout (key, false) := by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using ha
      exact ((entry.setMem (layout (key, true)) value).setMem_ne
        (layout (key, false)) a marker outside.2).trans
        (entry.setMem_ne (layout (key, true)) a value outside.1)

/-- Clearing one marker implements native erasure and leaves its payload
unchanged. The zero is an ordinary compiled constant, not an initialized
register or a free whole-table initialization step. -/
theorem erase_contract {κ : Type*} [DecidableEq κ] {heapLimit depth : Nat}
    {program : Program} {layout : κ × Bool → Word w}
    {map : Finmap (fun _ : κ => Word w)} (key : κ) (flagReg : Reg) :
    TotalRelContract program heapLimit depth (.store (.var flagReg) (.const 0))
      (fun s => FinmapAt heapLimit layout map s ∧ Function.Injective layout ∧
        s.regs flagReg = layout (key, false))
      (fun entry finish => finish = entry.setMem (layout (key, false)) 0 ∧
        FinmapAt heapLimit layout (map.erase key) finish ∧
        Set.EqOn finish.mem entry.mem ({layout (key, false)} : Set (Word w))ᶜ) := by
  apply Verification.verify_total_rel
  intro entry ⟨represented, injective, flag⟩
  apply Verification.TotalWP.store_iff.mpr
  refine ⟨trivial, trivial, ?_, ?_⟩
  · change (entry.regs flagReg).toNat < heapLimit
    rw [flag]
    exact represented.addr_lt (key, false)
  · have flagEval : entry.eval (.var flagReg) = layout (key, false) := flag
    have zeroEval : entry.eval (.const 0) = (0 : Word w) := rfl
    rw [flagEval, zeroEval]
    refine ⟨rfl, represented.setMem_erase injective key, ?_⟩
    intro a ha
    apply State.setMem_ne
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha

end Ram.Source.Finmap
