/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues

/-!
# Primitive rules for arena-aware core simulation

These rules reuse the existing measured lowering of local assignment, a
successful shared-object store, and result-field copying. They preserve the
actual arena cursor and placement; a write retains the source execution's
updated heap rather than replacing it by the entry heap.

The execution index is the supplied ordinary source execution. Scalar ranges,
descriptor lengths and sequential-copy separation retain their existing
meaning; no new execution relation or instruction price is introduced.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaCoreSimulates

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth cursor : Nat}
variable {entry : Complexity.Language.State Γ}

/-- Skipping keeps the actual state, arena and placement with zero instructions. -/
theorem skip
    {execution : Complexity.Language.Exec program
      (.skip : Complexity.Language.Stmt signatures Γ result) entry entry .normal} :
    ArenaCoreSimulates execution w heapLimit depth cursor cursor 0 := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  exact ⟨placement, s, .skip, ⟨matched, flagZero⟩, arena,
    Placement.Agrees.refl entry.heap placement, fun _ => matched⟩

/-- Assigning a source local uses the existing primitive count and preserves
the complete shared arena, including its metadata cursor. -/
theorem assign {τ : Ty} {target : Var Γ τ} {value : Prim Γ τ}
    {execution : Complexity.Language.Exec program
      (.assign target value : Complexity.Language.Stmt signatures Γ result)
      entry (entry.set target (value.eval entry.locals)) .normal}
    (fits : PrimFits w entry.locals value) :
    ArenaCoreSimulates execution w heapLimit depth cursor cursor (primCodeSize value) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  have assigned := lowerAssign_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout target value entry.locals s hw matched fits regular
  have matching : RegisterMap.Matches layout placement
      (entry.locals.set target (value.eval entry.locals))
      (s.setRegs (valueRegs τ (RegisterMap.base layout target))
        (valueWords placement (value.eval entry.locals))).regs :=
    lowerAssign_matches layout target value entry.locals s hw matched fits regular
  have flagPreserved := (valueRegs_setRegs_other s τ (RegisterMap.base layout target) flag
    (valueWords placement (value.eval entry.locals))
    (regular.not_mem_valueRegs_of_avoids avoids target)).trans flagZero
  exact ⟨placement, _, assigned, ⟨matching, flagPreserved⟩, arena.setRegs _ _,
    Placement.Agrees.refl entry.heap placement, fun _ => matching⟩

/-- A successful source write executes the same counted RAM store and retains
the actual updated source heap. Existing overlapping views remain permitted. -/
theorem write {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat} {value : Atom Γ kind.toTy} {heap : Complexity.Language.Heap}
    {written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
      (kind.ofValue (value.eval entry.locals)) = .ok heap}
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : ValueFits w (index.eval entry.locals))
    (valueFits : ValueFits w (value.eval entry.locals)) :
    ArenaCoreSimulates (.write (program := program) (result := result) written)
      w heapLimit depth cursor cursor writeCodeSize := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨measured, _⟩ := lowerWrite_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout buffer index value entry.locals s hw matched arena.heapRep
    bufferFits indexFits valueFits written
  rw [lowerWrite_stmtSize] at measured
  have cellFits : cellToNat (kind.ofValue (value.eval entry.locals)) < 2 ^ w := by
    cases kind <;> exact valueFits
  exact ⟨placement, _, measured, ⟨matched, flagZero⟩, arena.write written cellFits,
    Placement.Agrees.refl entry.heap placement, fun _ => matched⟩

/-- Returning pays for the actual result fields and the real flag assignment.
Final-local matching remains conditional on the existing copy-separation rule. -/
theorem ret {value : Atom Γ result}
    {execution : Complexity.Language.Exec program (.ret value) entry entry
      (.returned (value.eval entry.locals))}
    (fits : ValueFits w (value.eval entry.locals)) :
    ArenaCoreSimulates execution w heapLimit depth cursor cursor (2 * fieldCount result + 2) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  let received :=
    s.setRegs (valueRegs result resultSlot) (valueWords placement (value.eval entry.locals))
  have writeResult := lowerReturn_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout resultSlot value entry.locals s hw matched fits copySafe
  have raiseFlag : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign flag (.const 1)) 2 received (received.setReg flag 1) := .assign trivial
  refine ⟨placement, received.setReg flag 1, .seq writeResult raiseFlag, ?_,
    (arena.setRegs _ _).setReg flag 1, Placement.Agrees.refl entry.heap placement, ?_⟩
  · refine ⟨?_, Source.State.setReg_same received flag 1⟩
    rw [resultExprs_setReg_eval result resultSlot flag 1 received
      (flag_not_mem_valueRegs result resultSlot flag resultFlag)]
    exact resultExprs_setRegs_eval result resultSlot (value.eval entry.locals) s
  · intro separate
    have copied : layout.Matches placement entry.locals received.regs :=
      lowerReturn_matches layout resultSlot value entry.locals s matched separate
    intro τ v i
    exact RegisterMap.Matches.setReg_of_ne (entry := received) copied avoids 1 v i

end ArenaCoreSimulates
end Ram.LanguageCompiler
