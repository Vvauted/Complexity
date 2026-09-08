/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Finmap.Basic
import Complexity.Computability.Ram.Verification.StateM.Basic

/-!
# Reading a native optional finite-map value

The fixed lookup block reads a presence marker, then reads the payload only
when present. Its two result registers represent an ordinary `Option (Word w)`;
zero payload is still `some 0`, and an absent payload is never read. Runtime
address registers must already hold the key's two addresses.

The exact endpoint retains memory, I/O and unrelated registers. Its native
stateful model uses ordinary `get` and `pure`, not a new map evaluator.
The ghost key does not generate code. Address computation and initialization
remain outside this block; all loads and branches use the existing semantics.
-/

namespace Ram.Source.Finmap

/-- The presence result must not overwrite the still-needed payload address,
and the payload result must not overwrite the presence result. -/
def lookup (flagReg payloadReg found dst : Reg) : Stmt :=
  .seq (.assign found (.load (.var flagReg)))
    (.ite (.var found) (.assign dst (.load (.var payloadReg))) .skip)

/-- Read one optional value, retaining the whole finite map and the exact
state effect. If absent, the old payload-result register is left untouched. -/
theorem lookup_contract {κ : Type*} [DecidableEq κ] {heapLimit depth : Nat}
    {program : Program} {layout : κ × Bool → Word w}
    {map : Finmap (fun _ : κ => Word w)} (key : κ)
    (flagReg payloadReg found dst : Reg)
    (payload_available : payloadReg ≠ found) (found_retained : found ≠ dst) :
    TotalRelContract program heapLimit depth (lookup flagReg payloadReg found dst)
      (fun s => FinmapAt heapLimit layout map s ∧
        s.regs flagReg = layout (key, false) ∧ s.regs payloadReg = layout (key, true))
      (fun entry finish =>
        finish = (if entry.mem (layout (key, false)) = 0 then entry.setReg found 0
          else (entry.setReg found (entry.mem (layout (key, false)))).setReg dst
            (entry.mem (layout (key, true)))) ∧
        FinmapAt heapLimit layout map finish ∧
        (if finish.regs found = 0 then none else some (finish.regs dst)) = map.lookup key) := by
  apply Verification.verify_total_rel
  intro entry ⟨represented, flag, payload⟩
  rw [lookup, Verification.TotalWP.seq_iff]
  apply Verification.TotalWP.assign_iff.mpr
  refine ⟨⟨trivial, ?_⟩, ?_⟩
  · change (entry.regs flagReg).toNat < heapLimit
    rw [flag]
    exact represented.addr_lt (key, false)
  · have flagEval : entry.eval (.load (.var flagReg)) = entry.mem (layout (key, false)) := by
      simp [flag]
    rw [flagEval, Verification.TotalWP.ite_iff]
    refine ⟨trivial, ?_⟩
    simp only [State.eval_var, State.setReg_same]
    by_cases absent : entry.mem (layout (key, false)) = 0
    · rw [if_pos absent, Verification.TotalWP.skip_iff]
      refine ⟨by simp [absent], represented.setReg found _, ?_⟩
      rw [← represented.1.lookup key]
      simp [finmapLookup, absent]
    · rw [if_neg absent]
      apply Verification.TotalWP.assign_iff.mpr
      refine ⟨⟨trivial, ?_⟩, ?_⟩
      · change ((entry.setReg found _).regs payloadReg).toNat < heapLimit
        rw [State.setReg_ne _ _ _ _ payload_available, payload]
        exact represented.addr_lt (key, true)
      · have payloadEval : (entry.setReg found (entry.mem (layout (key, false)))).eval
            (.load (.var payloadReg)) = entry.mem (layout (key, true)) := by
          simp [payload_available, payload]
        rw [payloadEval]
        refine ⟨by rw [if_neg absent], (represented.setReg found _).setReg dst _, ?_⟩
        rw [← represented.1.lookup key]
        simp [finmapLookup, found_retained]

/-- The bound counts the real loads, moves, guard and branch jump. Safety and
termination are supplied separately by `lookup_contract`, not by this bound. -/
theorem lookup_timeBound {control heapLimit depth : Nat} {program : Program}
    (flagReg payloadReg found dst : Reg) :
    TimeBound control program heapLimit depth (lookup flagReg payloadReg found dst)
      (fun _ : State w => True) (fun _ => 9) := by
  intro entry _ steps finish execution
  cases execution with
  | seq first second =>
    cases first
    cases second with
    | iteTrue _ _ body => cases body; exact Nat.le_refl 9
    | iteFalse _ _ body => cases body; change 5 ≤ 9; decide

/-- Native state observation returns an optional lookup and leaves its map state
unchanged. The captured entry retains concrete frame information for clients. -/
theorem lookup_stateM {κ : Type} [DecidableEq κ] {heapLimit depth : Nat}
    {program : Program} {layout : κ × Bool → Word w} (key : κ)
    (flagReg payloadReg found dst : Reg)
    (payload_available : payloadReg ≠ found) (found_retained : found ≠ dst)
    (entry : State w) :
    Refines program heapLimit depth (lookup flagReg payloadReg found dst)
      (fun map s => s = entry ∧ FinmapAt heapLimit layout map s ∧
        s.regs flagReg = layout (key, false) ∧ s.regs payloadReg = layout (key, true))
      (fun result finish =>
        finish = (if entry.mem (layout (key, false)) = 0 then entry.setReg found 0
          else (entry.setReg found (entry.mem (layout (key, false)))).setReg dst
            (entry.mem (layout (key, true)))) ∧
        FinmapAt heapLimit layout result.2 finish ∧
        (if finish.regs found = 0 then none else some (finish.regs dst)) = result.1)
      (do
        let map ← get
        pure (map.lookup key) : StateM (Finmap (fun _ : κ => Word w)) (Option (Word w))).run := by
  rintro map s ⟨same, represented⟩
  subst s
  exact lookup_contract key flagReg payloadReg found dst payload_available found_retained
    entry represented

end Ram.Source.Finmap
