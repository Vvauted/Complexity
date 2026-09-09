/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation
import Complexity.Computability.Ram.Verification.Total

/-!
# Simulation of independent scalar source executions

The proof follows a source execution, not an evaluation of its compiled syntax.
The shared measured simulation supplies behavior by erasing its derived count;
no proposed time bound is needed and no second structural simulation is maintained.
Normal completion preserves the represented lexical values and a zero return
flag. A source return writes its actual result and sets the flag; enclosing
sequences then skip their remaining statements. Calls execute the selected
lowered function and restore caller locals, including the caller's private
flag, using the existing RAM calling convention. Each source child appears
only once in the generated structured code.

The final function theorem combines this generic simulation with an independent
mathematical source contract. Algorithm-specific register layouts or lowering
proofs are not premises. Word ranges and call nesting remain explicit source
realization conditions; an instruction-time bound is not required.

The source observation includes its explicit initial and final shared heaps.
This scalar bridge does not yet relate the source heap to RAM memory; its
register matching and target execution must not be read as a heap representation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {control : Control result}

/-- Initialize the private flag, run the core simulation, and dispatch an
arbitrary normal continuation. The continuation's own budget-free contract
supplies the final postcondition; returned paths bypass that continuation. -/
private theorem lower_of_core {entry finish : Env Γ} (hw : 0 < w)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout resultSlot flag finish control t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches entry s.regs →
      (control = .normal → ∀ t, layout.Matches finish t.regs →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords w value → post t) →
      Source.Verification.TotalWP (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) post s := by
  intro layout next resultSlot s continuation post bounded matched normal returned
  let flag := returnFlag result next resultSlot
  have nextFlag : next ≤ flag := Nat.le_max_left _ _
  have resultFlag : resultSlot + fieldCount result ≤ flag := Nat.le_max_right _ _
  have avoids : layout.Avoids flag := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (bounded v i) nextFlag)
  have bounded' : layout.Bounded (flag + 1) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_trans nextFlag (Nat.le_succ flag))
  have matched' : layout.Matches entry (s.setReg flag 0).regs :=
    RegisterMap.Matches.setReg_of_ne matched avoids 0
  obtain ⟨t, body, property⟩ := core layout (flag + 1) resultSlot flag (s.setReg flag 0)
    bounded' matched' avoids (Nat.lt_succ_self flag) resultFlag
    (Source.State.setReg_same s flag 0)
  have flagInit : Source.SafeExec (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) s (s.setReg flag 0) := .assign trivial
  cases control with
  | normal =>
      obtain ⟨u, tail, property'⟩ := normal rfl t property.1
      exact ⟨u, .seq flagInit (.seq body (.iteFalse trivial property.2 tail)), property'⟩
  | returned value =>
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq flagInit (.seq body (.iteTrue trivial raised .skip)),
        returned value rfl t property.1⟩
  | fault _ => exact False.elim property

/-- Simulate the linear-size core with its private flag already initialized.
All register separation belongs to the compiler proof; `lower` chooses these
slots and discharges these conditions for callers automatically. -/
theorem lowerCore (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout resultSlot flag finish.locals control t := by
  obtain ⟨steps, cost⟩ := execution.exists_cost
  intro layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
  obtain ⟨t, measured, property⟩ := cost.lowerCoreMeasured (heapLimit := heapLimit) 0 hw
    layout next resultSlot flag s bounded matched avoids fresh resultFlag flagZero
  exact ⟨t, measured.erase, property⟩

/-- Generic continuation simulation. Register preservation is needed only when
normal source completion reaches the continuation; a return supplies the actual
result fields instead. The target postcondition can therefore be chosen by a
caller without exposing a per-program register invariant. -/
theorem lower (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches entry.locals s.regs →
      (control = .normal → ∀ t, layout.Matches finish.locals t.regs →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords w value → post t) →
      Source.Verification.TotalWP (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) post s :=
  lower_of_core hw (execution.lowerCore hw)

/-- A returned source execution lowers to an invocation of the actual generated
function. Argument fields initialize its compact frame, and its declared result
expressions evaluate to the actual returned source value. -/
theorem functionExec {fn : Fin signatures.length}
    {args : Env signatures[fn].params} {initialHeap : Heap}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    (execution : RealizedExec program w depth (program.body fn)
      ⟨args, initialHeap⟩ finish (.returned value))
    (hw : 0 < w) (arguments : EnvFits w args) (s : Source.State w) :
    ∃ t, Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
      (envWords w args) s (valueWords w value) t := by
  obtain ⟨steps, cost⟩ := execution.exists_cost
  obtain ⟨t, measured⟩ :=
    cost.functionMeasuredExec (heapLimit := heapLimit) 0 hw arguments s
  exact ⟨t, measured.erase⟩

end RealizedExec

namespace FunctionRealizable

/-- Transfer a separately proved mathematical contract to the generated function.
Realization supplies ranges and nesting; source determinism supplies the same
actual returned value and final heap to the existing mathematical postcondition.
The source observation is retained without asserting a source-heap/RAM-memory
representation. -/
theorem functionExec {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (initialHeap : Heap)
    (arguments : EnvFits w args) (hfeasible : feasible args initialHeap)
    (hpre : pre args initialHeap) (s : Source.State w) :
    ∃ value finalHeap t,
      program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      Source.FunctionExec (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords w args) s (valueWords w value) t ∧
      post args initialHeap value finalHeap := by
  obtain ⟨finish, value, execution⟩ := realizable args initialHeap hfeasible
  obtain ⟨t, invocation⟩ := execution.functionExec hw arguments s
  exact ⟨value, finish.heap, t,
    Complexity.Language.Program.eval_eq_ok_iff.mpr ⟨finish, execution.erase, rfl⟩,
    invocation, specification.postcondition hpre execution.erase⟩

end FunctionRealizable

end Ram.LanguageCompiler
