/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Memory.Finmap.Contracts
import Ram.Memory.Finmap.Lookup
import Ram.Verification.StateM
import Ram.Verification.StateMComposition
import Ram.Verification.Specification
import Std.Tactic.Do

/-!
# Native stateful models for finite-map updates

The existing register-addressed store blocks refine ordinary `StateM.modify`
using mathlib's `Finmap.insert` and `Finmap.erase`. Keys, values and the entry
state are ghost parameters; they do not select the runtime program. The
preconditions retain the actual address and operand-register requirements.

Exact endpoint equalities preserve registers and I/O for later operations.
The standard `Set.EqOn` frames additionally expose unchanged heap locations,
so clients can retain unrelated represented objects without inspecting stores.
-/

namespace Ram.Source.Finmap

variable {κ : Type} [DecidableEq κ] {heapLimit depth : Nat} {program : Program}
variable {layout : κ × Bool → Word w}

/-- The verified two-store block refines native finite-map insertion. Its
complete endpoint retains all registers, including subsequent addresses. -/
theorem insert_stateM (entry : State w) (key : κ) (value marker : Word w)
    (payloadReg valueReg flagReg markerReg : Reg) :
    Refines program heapLimit depth
      (.seq (.store (.var payloadReg) (.var valueReg))
        (.store (.var flagReg) (.var markerReg)))
      (fun map s => s = entry ∧ FinmapAt heapLimit layout map s ∧
        Function.Injective layout ∧ marker ≠ 0 ∧
        s.regs payloadReg = layout (key, true) ∧ s.regs valueReg = value ∧
        s.regs flagReg = layout (key, false) ∧ s.regs markerReg = marker)
      (fun result finish =>
        finish = (entry.setMem (layout (key, true)) value).setMem
          (layout (key, false)) marker ∧
        FinmapAt heapLimit layout result.2 finish ∧
        Set.EqOn finish.mem entry.mem
          ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ)
      (modify (fun map : Finmap (fun _ : κ => Word w) => map.insert key value) :
        StateM (Finmap (fun _ : κ => Word w)) PUnit).run := by
  rintro map s ⟨same, represented⟩
  subst s
  exact insert_contract key value marker payloadReg valueReg flagReg markerReg
    entry represented

/-- Clearing the presence marker refines native erasure, without changing the
payload or any register. The heap frame is retained for subsequent clients. -/
theorem erase_stateM (entry : State w) (key : κ) (flagReg : Reg) :
    Refines program heapLimit depth (.store (.var flagReg) (.const 0))
      (fun map s => s = entry ∧ FinmapAt heapLimit layout map s ∧
        Function.Injective layout ∧ s.regs flagReg = layout (key, false))
      (fun result finish => finish = entry.setMem (layout (key, false)) 0 ∧
        FinmapAt heapLimit layout result.2 finish ∧
        Set.EqOn finish.mem entry.mem ({layout (key, false)} : Set (Word w))ᶜ)
      (modify (fun map : Finmap (fun _ : κ => Word w) => map.erase key) :
        StateM (Finmap (fun _ : κ => Word w)) PUnit).run := by
  rintro map s ⟨same, represented⟩
  subst s
  exact erase_contract key flagReg entry represented

/-- Compose insertion and lookup through native monadic bind. The read-after-write
law is proved by native `mvcgen` and mathlib, then retained in the refinement.
Only the two existing implementation refinements handle machine execution.
All operand-register requirements remain explicit, including those needed after
the insertion. A zero payload is returned as `some 0`, not as absence. -/
theorem insert_lookup_stateM (entry : State w) (key : κ) (value marker : Word w)
    (payloadReg valueReg flagReg markerReg found dst : Reg)
    (injective : Function.Injective layout) (nonzero : marker ≠ 0)
    (payload : entry.regs payloadReg = layout (key, true))
    (stored : entry.regs valueReg = value)
    (flag : entry.regs flagReg = layout (key, false))
    (presence : entry.regs markerReg = marker)
    (payload_available : payloadReg ≠ found) (found_retained : found ≠ dst) :
    let updated := (entry.setMem (layout (key, true)) value).setMem
      (layout (key, false)) marker
    Refines program heapLimit depth
      (.seq (.seq (.store (.var payloadReg) (.var valueReg))
        (.store (.var flagReg) (.var markerReg)))
        (lookup flagReg payloadReg found dst))
      (fun map s => s = entry ∧ FinmapAt heapLimit layout map s)
      (fun result finish => finish = (updated.setReg found marker).setReg dst value ∧
        FinmapAt heapLimit layout result.2 finish ∧
        (if finish.regs found = 0 then none else some (finish.regs dst)) = result.1 ∧
        result.1 = some value ∧
        Set.EqOn finish.mem entry.mem
          ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ)
      (do
        modify (fun map : Finmap (fun _ : κ => Word w) => map.insert key value)
        let map ← get
        pure (map.lookup key) :
        StateM (Finmap (fun _ : κ => Word w)) (Option (Word w))).run := by
  dsimp only
  let updated := (entry.setMem (layout (key, true)) value).setMem
    (layout (key, false)) marker
  have composed := (insert_stateM (program := program) (heapLimit := heapLimit)
    (depth := depth) (layout := layout) entry key value marker
      payloadReg valueReg flagReg markerReg).stateM_bind
    (next := fun _ => do
      let map ← get
      pure (map.lookup key))
    (outputRep := fun result finish =>
      finish = (updated.setReg found marker).setReg dst value ∧
      FinmapAt heapLimit layout result.2 finish ∧
      (if finish.regs found = 0 then none else some (finish.regs dst)) = result.1 ∧
      Set.EqOn finish.mem entry.mem
        ({layout (key, true), layout (key, false)} : Set (Word w))ᶜ) (fun _ => by
      rintro map middle ⟨same, represented, frame⟩
      apply Verification.TotalWP.of_contract
        ((lookup_stateM (program := program) (heapLimit := heapLimit) (depth := depth)
          (layout := layout) key flagReg payloadReg found dst
          payload_available found_retained updated) map)
      · exact ⟨same, represented, by simpa [same, updated] using flag,
          by simpa [same, updated] using payload⟩
      · rintro finish ⟨endpoint, result, observed⟩
        refine ⟨?_, result, observed, ?_⟩
        · have flagValue : updated.mem (layout (key, false)) = marker :=
            State.setMem_same _ _ _
          have payloadValue : updated.mem (layout (key, true)) = value := by
            simp [updated, injective.eq_iff]
          rw [flagValue, if_neg nonzero, payloadValue] at endpoint
          exact endpoint
        · have unchanged : finish.mem = middle.mem := by
            rw [endpoint, same]
            split <;> rfl
          rw [unchanged]
          exact frame)
  have model_spec : Std.Do.Triple
      (ps := .arg (Finmap (fun _ : κ => Word w)) .pure)
      (do
        modify (fun map : Finmap (fun _ : κ => Word w) => map.insert key value)
        let map ← get
        pure (map.lookup key) :
        StateM (Finmap (fun _ : κ => Word w)) (Option (Word w)))
      (fun _ => ⟨True⟩) (fun result _ => ⟨result = some value⟩, ⟨⟩) := by
    mvcgen
    exact _root_.Finmap.lookup_insert _
  have strengthened := composed.stateM_spec_refines model_spec
  intro map
  apply (strengthened map).consequence
  · rintro s ⟨same, represented⟩
    subst s
    exact ⟨⟨rfl, represented, injective, nonzero, payload, stored, flag, presence⟩,
      trivial⟩
  · rintro finish ⟨⟨endpoint, represented, observed, frame⟩, property⟩
    exact ⟨endpoint, represented, observed, property, frame⟩

end Ram.Source.Finmap
