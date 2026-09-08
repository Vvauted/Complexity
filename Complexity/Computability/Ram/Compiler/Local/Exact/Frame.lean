/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.ABI.Slots
import Complexity.Computability.Ram.Compiler.Local.Exact.WritesBasic

/-!
# Older saved frames at every compiled execution prefix

The write-region simulation excludes every address in the interval from the
source heap boundary to entry SP. Monotonicity of the actual cumulative write
set then preserves those words at every execution prefix. In particular, an
older frame retains its return address and all saved locals while an arbitrary
nested statement executes, including calls and loops.

The saved frame may have any local count and any base in the protected interval.
Its location, contents and return word are fixed at entry; no ownership claim
is made about the source heap or the newer stack region.
-/

namespace Ram.LocalCompiler.SimulationWrites

variable {control locals heapLimit depth steps : Nat} {code : Code}
variable {localsTable entries : Nat → Nat} {stmt : Stmt} {s s' : Source.State w}
variable (simulation : SimulationWrites control locals heapLimit code localsTable entries
  depth stmt steps s s') (hlocals : locals ≤ control) {start : State w}
variable (matched : Source.State.Matches heapLimit locals s start)
variable (lower : heapLimit ≤ (start.regs (ABI.sp control)).toNat)
variable (fits : Compiler.StackFits control depth start)
variable (atStmt : CodeAt code start.pc (compileStmt control localsTable entries stmt start.pc))

include simulation hlocals matched lower fits atStmt

/-- No actual transition in the entire simulated statement writes an older
stack word, even if that transition would store the word's existing value. -/
theorem not_mem_heapWrites_of_older {address : Word w}
    (aboveHeap : heapLimit ≤ address.toNat)
    (belowStack : address.toNat < (start.regs (ABI.sp control)).toNat) :
    address ∉ heapWrites code steps start := by
  intro member
  rcases simulation.2 hlocals start matched lower fits atStmt address member with source | stack
  · exact (Nat.not_lt_of_ge aboveHeap) source
  · exact (Nat.not_le_of_lt belowStack) stack

/-- Every real prefix preserves an older word, including both endpoints. -/
theorem prefix_mem_eq_of_older {k : Nat} {current : State w}
    (hk : k ≤ steps) (execution : Exec code k start current) {address : Word w}
    (aboveHeap : heapLimit ≤ address.toNat)
    (belowStack : address.toNat < (start.regs (ABI.sp control)).toNat) :
    current.mem address = start.mem address :=
  execution.prefix_mem_eq_of_not_written hk
    (simulation.not_mem_heapWrites_of_older hlocals matched lower fits atStmt aboveHeap belowStack)

/-- An older frame's complete concrete slot set is disjoint from all writes
of the simulated statement. Its fit follows from its location below entry SP. -/
theorem frameSlots_disjoint_heapWrites {base : Word w} {savedLocals : Nat}
    (baseLower : heapLimit ≤ base.toNat)
    (frameUpper : base.toNat + ABI.frameSize savedLocals ≤
      (start.regs (ABI.sp control)).toNat) :
    Disjoint (ABI.frameSlots base savedLocals) (heapWrites code steps start) := by
  have frameFit : base.toNat + ABI.frameSize savedLocals ≤ 2 ^ w :=
    frameUpper.trans (Nat.le_of_lt (BitVec.isLt _))
  apply Finset.disjoint_left.mpr
  intro address member written
  have bounds := (ABI.mem_frameSlots_iff frameFit).mp member
  exact simulation.not_mem_heapWrites_of_older hlocals matched lower fits atStmt
    (baseLower.trans bounds.1) (bounds.2.trans_le frameUpper) written

/-- All words of a fixed older frame retain their entry values throughout
every actual prefix, without requiring a separately supplied no-wrap premise. -/
theorem prefix_frameSlots_mem_eq {base : Word w} {savedLocals k : Nat} {current : State w}
    (baseLower : heapLimit ≤ base.toNat)
    (frameUpper : base.toNat + ABI.frameSize savedLocals ≤
      (start.regs (ABI.sp control)).toNat)
    (hk : k ≤ steps) (execution : Exec code k start current) :
    ∀ address ∈ ABI.frameSlots base savedLocals, current.mem address = start.mem address := by
  have separate := simulation.frameSlots_disjoint_heapWrites hlocals matched lower fits atStmt
    baseLower frameUpper
  intro address member
  exact execution.prefix_mem_eq_of_not_written hk
    (fun written => Finset.disjoint_left.mp separate member written)

/-- A previously established saved frame and its return address survive
together at every real prefix of a nested statement. The register values are
the original saved values, not the nested statement's current registers. -/
theorem prefix_savedFrame {base returnWord : Word w} {savedLocals k : Nat}
    {savedRegs : Reg → Word w} {current : State w}
    (baseLower : heapLimit ≤ base.toNat)
    (frameUpper : base.toNat + ABI.frameSize savedLocals ≤
      (start.regs (ABI.sp control)).toNat)
    (saved : ABI.FrameSaved savedLocals base savedRegs start.mem)
    (header : start.mem base = returnWord)
    (hk : k ≤ steps) (execution : Exec code k start current) :
    current.mem base = returnWord ∧ ABI.FrameSaved savedLocals base savedRegs current.mem := by
  have preserved := simulation.prefix_frameSlots_mem_eq hlocals matched lower fits atStmt
    baseLower frameUpper hk execution
  constructor
  · exact (preserved base (by simp only [ABI.frameSlots, Finset.mem_union,
      Finset.mem_singleton, true_or])).trans header
  · apply saved.congr
    intro i hi
    apply preserved
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩)

end Ram.LocalCompiler.SimulationWrites
