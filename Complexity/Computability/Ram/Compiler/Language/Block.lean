/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation
import Complexity.Computability.Ram.Compiler.Language.Effects

/-!
# Value-producing blocks with continuing local state

A block can return a value while its enclosing computation continues. In
particular, an effectful loop guard must hand its actual final locals and heap
to the body; function-call restoration would discard those local updates.

`lowerBlock` reserves a fresh result tuple and its own return flag. The shared
simulation supplies both the value and the updated source environment. Static
write frames preserve surrounding private control registers, even when the
block calls functions or mutates the shared heap. Counts include real flag
initialization; no loop semantics or termination assumption is supplied here.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ExecutionCost

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w depth heapLimit steps : Nat}
variable {placement : Nat → Word w}
variable {block : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {value : Value result}
variable {execution : RealizedExec program w depth block entry finish (.returned value)}

/-- A returned block leaves its actual value, locals and heap available to its
enclosing computation. Generated fresh result slots supply the separation; an
algorithm author does not prove a second register-level implementation. -/
theorem lowerBlockMeasured (cost : ExecutionCost execution steps) (controlReg : Nat)
    (hw : 0 < w) (layout : RegisterMap Γ) (next : Reg) (s : Source.State w)
    (regular : layout.Regular) (bounded : layout.Bounded next)
    (matched : layout.Matches placement entry.locals s.regs)
    (represented : HeapRep placement heapLimit entry.heap s) :
    ∃ t, Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerBlock layout next block) (steps + 2) s t ∧
      layout.Matches placement finish.locals t.regs ∧
      (resultExprs result next).map t.eval = valueWords placement value ∧
      HeapRep placement heapLimit finish.heap t ∧
      ∀ r, r < next → layout.Avoids r → t.regs r = s.regs r := by
  let flag := next + fieldCount result
  have nextFlag : next ≤ flag := Nat.le_add_right _ _
  have bounded' : layout.Bounded (flag + 1) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (nextFlag.trans (Nat.le_succ flag))
  have avoids : layout.Avoids flag := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (bounded v i) nextFlag)
  have separated : layout.AvoidsRange next (fieldCount result) := bounded.avoidsRange _
  have initialized : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) 2 s (s.setReg flag 0) := .assign trivial
  obtain ⟨t, body, returned, finalHeap, finalLocals⟩ :=
    cost.lowerCoreMeasuredWithLocals (heapLimit := heapLimit) controlReg hw
      layout (flag + 1) next flag (s.setReg flag 0) regular bounded'
      (matched.setReg_of_ne avoids 0) avoids (Nat.lt_succ_self flag)
      (Nat.le_refl flag) (Or.inr separated) (represented.setReg flag 0)
      (Source.State.setReg_same s flag 0)
  refine ⟨t, ?_, finalLocals separated, returned.1, finalHeap, ?_⟩
  · simpa only [lowerBlock, flag, Nat.add_comm] using
      Source.LocalMeasuredExec.seq initialized body
  · intro r before outside
    have different : r ≠ flag := Nat.ne_of_lt (Nat.lt_of_lt_of_le before nextFlag)
    have resultOutside : r ∉ valueRegs result next := by
      intro member
      exact Nat.not_le_of_gt before (mem_valueRegs.mp member).1
    have preserved := lowerStmtCore_regs_eq body.erase regular bounded' outside
      (Nat.lt_of_lt_of_le before (nextFlag.trans (Nat.le_succ flag))) resultOutside different
    exact preserved.trans (Source.State.setReg_ne s flag r 0 different)

end ExecutionCost

namespace RealizedExec

/-- Forgetting the count gives the same block execution and actual continuing
state, without a source time budget or a callee-local restoration step. -/
theorem lowerBlock {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {w depth heapLimit : Nat} {placement : Nat → Word w}
    {block : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {value : Value result}
    (execution : RealizedExec program w depth block entry finish (.returned value))
    (hw : 0 < w) (layout : RegisterMap Γ) (next : Reg) (s : Source.State w)
    (regular : layout.Regular) (bounded : layout.Bounded next)
    (matched : layout.Matches placement entry.locals s.regs)
    (represented : HeapRep placement heapLimit entry.heap s) :
    ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (LanguageCompiler.lowerBlock layout next block) s t ∧
      layout.Matches placement finish.locals t.regs ∧
      (resultExprs result next).map t.eval = valueWords placement value ∧
      HeapRep placement heapLimit finish.heap t ∧
      ∀ r, r < next → layout.Avoids r → t.regs r = s.regs r := by
  obtain ⟨steps, cost⟩ := execution.exists_cost
  obtain ⟨t, measured, locals, result, heap, preserved⟩ :=
    cost.lowerBlockMeasured 0 hw layout next s regular bounded matched represented
  exact ⟨t, measured.erase, locals, result, heap, preserved⟩

end RealizedExec

end Ram.LanguageCompiler
