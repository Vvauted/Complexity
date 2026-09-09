/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation
import Complexity.Computability.Ram.Verification.Total

/-!
# Simulation of independent source executions

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

One fixed placement relates the explicit initial and final source heaps to RAM
memory. Calls and continuations retain the actual final heap representation,
separately from lexical matching and the encoded return fields.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth heapLimit : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {control : Control result}
variable {placement : Nat → Word w}

/-- Initialize the private flag, run the core simulation, and dispatch an
arbitrary normal continuation. The continuation's own budget-free contract
supplies the final postcondition; returned paths bypass that continuation. -/
private theorem lower_of_core (hw : 0 < w)
    (core : ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout placement resultSlot flag finish.locals control t ∧
        HeapRep placement heapLimit finish.heap t) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches placement entry.locals s.regs →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s →
      (control = .normal → ∀ t, layout.Matches placement finish.locals t.regs →
        HeapRep placement heapLimit finish.heap t →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords placement value →
        HeapRep placement heapLimit finish.heap t → post t) →
      Source.Verification.TotalWP (lowerProgram program) heapLimit depth
        (lowerStmt layout next resultSlot stmt continuation) post s := by
  intro layout next resultSlot s continuation post bounded matched copySafe represented
    normal returned
  let flag := returnFlag result next resultSlot
  have nextFlag : next ≤ flag := Nat.le_max_left _ _
  have resultFlag : resultSlot + fieldCount result ≤ flag := Nat.le_max_right _ _
  have avoids : layout.Avoids flag := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (bounded v i) nextFlag)
  have bounded' : layout.Bounded (flag + 1) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_trans nextFlag (Nat.le_succ flag))
  have matched' : layout.Matches placement entry.locals (s.setReg flag 0).regs :=
    RegisterMap.Matches.setReg_of_ne matched avoids 0
  obtain ⟨t, body, property, finalHeap⟩ :=
    core layout (flag + 1) resultSlot flag (s.setReg flag 0)
      bounded' matched' avoids (Nat.lt_succ_self flag) resultFlag copySafe
      (represented.setReg flag 0) (Source.State.setReg_same s flag 0)
  have flagInit : Source.SafeExec (lowerProgram program) heapLimit depth
      (.assign flag (.const 0)) s (s.setReg flag 0) := .assign trivial
  cases control with
  | normal =>
      obtain ⟨u, tail, property'⟩ := normal rfl t property.1 finalHeap
      exact ⟨u, .seq flagInit (.seq body (.iteFalse trivial property.2 tail)), property'⟩
  | returned value =>
      have raised : t.eval (.var flag) ≠ 0 := by
        change t.regs flag ≠ 0
        rw [property.2]
        exact Word.one_ne_zero hw
      exact ⟨t, .seq flagInit (.seq body (.iteTrue trivial raised .skip)),
        returned value rfl t property.1 finalHeap⟩
  | fault _ => exact False.elim property

/-- Simulate the linear-size core with its private flag already initialized.
The wrapper infers flag separation; multi-field return-copy separation and
the current shared-heap representation remain explicit compiler premises. -/
theorem lowerCore (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot flag : Reg) (s : Source.State w),
      layout.Bounded next → layout.Matches placement entry.locals s.regs → layout.Avoids flag →
      flag < next → resultSlot + fieldCount result ≤ flag →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s → s.regs flag = 0 →
      ∃ t, Source.SafeExec (lowerProgram program) heapLimit depth
        (lowerStmtCore layout next resultSlot flag stmt) s t ∧
        ControlMatches layout placement resultSlot flag finish.locals control t ∧
        HeapRep placement heapLimit finish.heap t := by
  obtain ⟨steps, cost⟩ := execution.exists_cost
  intro layout next resultSlot flag s bounded matched avoids fresh resultFlag copySafe
    represented flagZero
  obtain ⟨t, measured, property, finalHeap⟩ := cost.lowerCoreMeasured (heapLimit := heapLimit) 0 hw
    layout next resultSlot flag s bounded matched avoids fresh resultFlag copySafe represented flagZero
  exact ⟨t, measured.erase, property, finalHeap⟩

/-- Generic continuation simulation. Register preservation is needed only when
normal source completion reaches the continuation; a return supplies the actual
result fields instead. The target postcondition can therefore be chosen by a
caller without exposing a per-program register invariant. -/
theorem lower (execution : RealizedExec program w depth stmt entry finish control)
    (hw : 0 < w) :
    ∀ (layout : RegisterMap Γ) (next resultSlot : Reg) (s : Source.State w)
      (continuation : Ram.Stmt) (post : Source.State w → Prop),
      layout.Bounded next → layout.Matches placement entry.locals s.regs →
      (fieldCount result ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount result)) →
      HeapRep placement heapLimit entry.heap s →
      (control = .normal → ∀ t, layout.Matches placement finish.locals t.regs →
        HeapRep placement heapLimit finish.heap t →
        Source.Verification.TotalWP (lowerProgram program) heapLimit depth
          continuation post t) →
      (∀ value, control = .returned value → ∀ t,
        (resultExprs result resultSlot).map t.eval = valueWords placement value →
        HeapRep placement heapLimit finish.heap t → post t) →
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
    (hw : 0 < w) (arguments : EnvFits w args) (s : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap s) :
    ∃ t, Source.FunctionExec (lowerProgram program) heapLimit depth (lowerFunc program fn)
      (envWords placement args) s (valueWords placement value) t ∧
      HeapRep placement heapLimit finish.heap t := by
  obtain ⟨steps, cost⟩ := execution.exists_cost
  obtain ⟨t, measured, finalHeap⟩ :=
    cost.functionMeasuredExec (heapLimit := heapLimit) 0 hw arguments s represented
  exact ⟨t, measured.erase, finalHeap⟩

end RealizedExec

namespace FunctionRealizable

/-- Transfer a separately proved mathematical contract to the generated function.
Realization supplies ranges and nesting; source determinism supplies the same
actual returned value and final heap to the existing mathematical postcondition.
The same invocation represents that final source heap under the fixed placement. -/
theorem functionExec {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth heapLimit : Nat}
    {placement : Nat → Word w}
    {fn : Fin signatures.length} {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (hw : 0 < w) (args : Env signatures[fn].params) (initialHeap : Heap)
    (arguments : EnvFits w args) (hfeasible : feasible args initialHeap)
    (hpre : pre args initialHeap) (s : Source.State w)
    (represented : HeapRep placement heapLimit initialHeap s) :
    ∃ value finalHeap t,
      program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      Source.FunctionExec (lowerProgram program) heapLimit depth
        (lowerFunc program fn) (envWords placement args) s (valueWords placement value) t ∧
      post args initialHeap value finalHeap ∧
      HeapRep placement heapLimit finalHeap t := by
  obtain ⟨finish, value, execution⟩ := realizable args initialHeap hfeasible
  obtain ⟨t, invocation, representedFinal⟩ := execution.functionExec hw arguments s represented
  exact ⟨value, finish.heap, t,
    Complexity.Language.Program.eval_eq_ok_iff.mpr ⟨finish, execution.erase, rfl⟩,
    invocation, specification.postcondition hpre execution.erase, representedFinal⟩

end FunctionRealizable

end Ram.LanguageCompiler
