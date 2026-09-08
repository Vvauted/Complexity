/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Function
import Complexity.Computability.Ram.Source.Function.Basic

/-!
# Endpoint frames for local register updates

`State.LocalFrame writes entry finish` states that shared memory and input/output
are unchanged, and registers outside `writes` agree at the two endpoints. Its
register component is mathlib's `Set.EqOn`, not a separate collection interface.

The set allows endpoint changes; it is neither an actual write-event trace nor
a static effect analysis. A register may be written and restored between these
endpoints. The shared-state equalities are genuine premises of this particular
relation, not claims that general heap-mutating or stream operations are pure.
Parameter entry changes the entire register environment; local initialization
is framed relative to that already-entered state, not to guessed fresh locals.
-/

namespace Ram.Source.State

/-- Restoring caller registers recovers the caller state when all actual shared
effects are unchanged. No property of discarded callee registers is required. -/
theorem restore_eq_of_shared {entry finish : State w}
    (memory : finish.mem = entry.mem) (input : finish.input = entry.input)
    (output : finish.outputRev = entry.outputRev) : entry.restore finish = entry := by
  cases entry
  cases finish
  simp_all only [restore]

/-- Shared state is unchanged, and only the allowed local registers may differ
between the existing states. This proposition does not describe an execution. -/
structure LocalFrame (writes : Set Reg) (entry finish : State w) : Prop where
  mem : finish.mem = entry.mem
  input : finish.input = entry.input
  outputRev : finish.outputRev = entry.outputRev
  regs : Set.EqOn finish.regs entry.regs writesᶜ

namespace LocalFrame

variable {writes writes' observed : Set Reg} {entry middle finish : State w}

/-- Identical endpoints satisfy every allowed-change frame. -/
theorem refl (writes : Set Reg) (entry : State w) : LocalFrame writes entry entry :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Enlarging the allowed-change set weakens the endpoint assertion. -/
theorem mono (h : LocalFrame writes entry finish) (subset : writes ⊆ writes') :
    LocalFrame writes' entry finish :=
  ⟨h.mem, h.input, h.outputRev,
    Set.EqOn.mono (fun _ outside inside => outside (subset inside)) h.regs⟩

/-- Sequential endpoint frames allow the union of the two change sets. -/
theorem trans (first : LocalFrame writes entry middle)
    (second : LocalFrame writes' middle finish) :
    LocalFrame (writes ∪ writes') entry finish := by
  refine ⟨second.mem.trans first.mem, second.input.trans first.input,
    second.outputRev.trans first.outputRev, ?_⟩
  exact (Set.EqOn.mono (s₁ := (writes ∪ writes')ᶜ)
    (fun _ outside inside => outside (Or.inr inside)) second.regs).trans
    (Set.EqOn.mono (s₁ := (writes ∪ writes')ᶜ)
      (fun _ outside inside => outside (Or.inl inside)) first.regs)

/-- One actual register assignment preserves all other locals and shared state. -/
theorem setReg (entry : State w) (dst : Reg) (value : Word w) :
    LocalFrame {dst} entry (entry.setReg dst value) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro r outside
  exact State.setReg_ne entry dst r value (by simpa using outside)

/-- Ordered assignment changes only listed destinations. Repeated destinations
and unequal list lengths retain the existing last-write and truncation semantics. -/
theorem setRegs (entry : State w) (dsts : List Reg) (values : List (Word w)) :
    LocalFrame {r | r ∈ dsts} entry (entry.setRegs dsts values) :=
  ⟨State.setRegs_mem entry dsts values, State.setRegs_input entry dsts values,
    State.setRegs_outputRev entry dsts values,
    fun r outside => State.setRegs_ne entry dsts values r outside⟩

/-- Reading outside the allowed-change set gives the original local value. -/
theorem reg_eq (h : LocalFrame writes entry finish) {r : Reg} (outside : r ∉ writes) :
    finish.regs r = entry.regs r :=
  h.regs outside

/-- Every disjoint collection of protected registers retains its values. -/
theorem eqOn (h : LocalFrame writes entry finish) (separated : Disjoint observed writes) :
    Set.EqOn finish.regs entry.regs observed :=
  Set.EqOn.mono (fun _ member => separated.notMem_of_mem_left member) h.regs

/-- Discarding the local changes recovers the entire original state. -/
theorem restore_eq (h : LocalFrame writes entry finish) : entry.restore finish = entry :=
  restore_eq_of_shared h.mem h.input h.outputRev

end LocalFrame

end Ram.Source.State
