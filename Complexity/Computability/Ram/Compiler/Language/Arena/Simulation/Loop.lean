/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation

/-!
# Allocating loop simulation

These composition lemmas use callbacks for the guard, body and remaining source
execution. Each callback consumes the preceding execution's actual heap,
placement and arena cursor. In particular, an effectful guard supplies its final
lexical bindings to the body, including when returning its Boolean result.

The measured executions are those of the existing RAM lowering. Their loop
administration costs are independent of the allocation work in the callbacks.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaCoreSimulates

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth : Nat}

/-- Run a guard with its private Boolean result and return flag. The enclosing
flag is preserved, while the guard's actual final locals and arena are retained. -/
theorem lowerGuard
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {entry guardFinish : Complexity.Language.State Γ} {choice : Bool}
    {cursor finalCursor guardSteps : Nat}
    (test : Complexity.Language.Exec program guard entry guardFinish (.returned choice))
    (core : ArenaCoreSimulates test w heapLimit depth cursor finalCursor guardSteps)
    (controlReg : Nat) (hw : 0 < w) (placement : Nat → Word w)
    (layout : RegisterMap Γ) (next outerFlag : Reg) (s : Source.State w)
    (regular : RegisterMap.Regular layout) (bounded : layout.Bounded next)
    (matched : layout.Matches placement entry.locals s.regs)
    (avoids : layout.Avoids outerFlag) (fresh : outerFlag < next)
    (rooted : entry.locals.Rooted entry.heap)
    (represented : ArenaRep placement cursor heapLimit entry.heap s)
    (flagZero : s.regs outerFlag = 0) :
    ∃ finalPlacement t,
      Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
        (lowerStmtCore layout (next + 2) next (next + 1) guard) guardSteps
          ((s.setReg next 1).setReg (next + 1) 0) t ∧
      layout.Matches finalPlacement guardFinish.locals t.regs ∧
      ArenaRep finalPlacement finalCursor heapLimit guardFinish.heap t ∧
      Placement.Agrees entry.heap placement finalPlacement ∧
      t.regs next = (if choice then 1 else 0) ∧ t.regs outerFlag = 0 := by
  have avoidsTest : layout.Avoids next := by
    intro τ v i
    exact Nat.ne_of_lt (bounded v i)
  have avoidsGuardFlag : layout.Avoids (next + 1) := by
    intro τ v i
    exact Nat.ne_of_lt (Nat.lt_trans (bounded v i) (Nat.lt_succ_self next))
  have bounded' : layout.Bounded (next + 2) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_add_right next 2)
  have activeMatches : layout.Matches placement entry.locals (s.setReg next 1).regs :=
    RegisterMap.Matches.setReg_of_ne matched avoidsTest 1
  have preparedMatches : layout.Matches placement entry.locals
      ((s.setReg next 1).setReg (next + 1) 0).regs :=
    RegisterMap.Matches.setReg_of_ne activeMatches avoidsGuardFlag 0
  obtain ⟨finalPlacement, t, measured, property, finalArena, agreed, finalMatches⟩ :=
    core controlReg hw placement layout (next + 2) next (next + 1) _
      regular bounded' preparedMatches avoidsGuardFlag (Nat.lt_succ_self (next + 1))
      (Nat.le_refl _) (Or.inl (Nat.le_refl 1)) rooted
      ((represented.setReg next 1).setReg (next + 1) 0)
      (Source.State.setReg_same _ _ _)
  have tested : t.regs next = (if choice then 1 else 0) := by
    cases choice <;> simpa [resultExprs, Source.State.eval, Expr.eval] using property.1
  have flagPreserved := lowerStmtCore_regs_eq (r := outerFlag) measured.erase
    regular bounded' avoids (Nat.lt_of_lt_of_le fresh (Nat.le_add_right next 2))
    (flag_not_mem_valueRegs_of_lt .bool next outerFlag fresh)
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le fresh (Nat.le_add_right next 1)))
  have unchanged : t.regs outerFlag = 0 := by
    rw [flagPreserved,
      Source.State.setReg_ne _ _ _ _
        (Nat.ne_of_lt (Nat.lt_of_lt_of_le fresh (Nat.le_add_right next 1))),
      Source.State.setReg_ne _ _ _ _ (Nat.ne_of_lt fresh), flagZero]
  exact ⟨finalPlacement, t, measured, finalMatches (bounded.avoidsRange _),
    finalArena, agreed, tested, unchanged⟩

/-- A false guard retains its heap effects and ends the loop normally. -/
theorem whileFalse
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {cursor finalCursor guardSteps : Nat}
    (test : Complexity.Language.Exec program guard entry finish (.returned false))
    (guardCore : ArenaCoreSimulates test w heapLimit depth cursor finalCursor guardSteps) :
    ArenaCoreSimulates (Complexity.Language.Exec.whileFalse (body := body) test)
      w heapLimit depth cursor finalCursor (guardSteps + 11) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched
    avoids fresh resultFlag copySafe rooted represented flagZero
  obtain ⟨finalPlacement, t, guardRun, guardMatches, finalArena, agreed, tested,
      preservedFlag⟩ :=
    lowerGuard test guardCore controlReg hw placement layout next flag s regular bounded
      matched avoids fresh rooted represented flagZero
  have initialized : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign next (.const 1)) 2 s (s.setReg next 1) := .assign trivial
  have reset : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign (next + 1) (.const 0)) 2 (s.setReg next 1)
        ((s.setReg next 1).setReg (next + 1) 0) := .assign trivial
  have active : (s.setReg next 1).eval (.var next) ≠ 0 := by
    change (s.setReg next 1).regs next ≠ 0
    rw [Source.State.setReg_same]
    exact Word.one_ne_zero hw
  have dispatch : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.ite (.var next)
        (.seq (lowerStmtCore layout (next + 2) resultSlot flag body)
          (.ite (.var flag) (.assign next (.const 0)) .skip)) .skip) 2 t t :=
    .iteFalse (c := .var next) trivial tested .skip
  refine ⟨finalPlacement, t, ?_, ⟨guardMatches, preservedFlag⟩, finalArena,
    agreed, fun _ => guardMatches⟩
  convert Source.LocalMeasuredExec.seq initialized
    (Source.LocalMeasuredExec.whileTrue (c := .var next) trivial active
      (.seq reset (.seq guardRun dispatch))
      (.whileFalse (c := .var next) trivial tested)) using 1
  simp only [Expr.compile, List.length_singleton]
  omega

/-- A normal iteration threads the guard and body arenas into the remaining
loop, without counting the tail's already-satisfied initialization twice. -/
theorem whileTrue
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {entry afterGuard afterBody finish : Complexity.Language.State Γ}
    {outcome : Control result}
    {cursor guardCursor bodyCursor finalCursor guardSteps bodySteps restSteps : Nat}
    (test : Complexity.Language.Exec program guard entry afterGuard (.returned true))
    (iteration : Complexity.Language.Exec program body afterGuard afterBody .normal)
    (rest : Complexity.Language.Exec program (.while guard body) afterBody finish outcome)
    (guardCore : ArenaCoreSimulates test w heapLimit depth cursor guardCursor guardSteps)
    (bodyCore : ArenaCoreSimulates iteration w heapLimit depth guardCursor bodyCursor bodySteps)
    (restCore : ArenaCoreSimulates rest w heapLimit depth bodyCursor finalCursor restSteps) :
    ArenaCoreSimulates (Complexity.Language.Exec.whileTrue test iteration rest)
      w heapLimit depth cursor finalCursor (guardSteps + bodySteps + restSteps + 10) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched
    avoids fresh resultFlag copySafe rooted represented flagZero
  obtain ⟨guardPlacement, guardTarget, guardRun, guardMatches, guardArena, guardAgrees,
      tested, preservedFlag⟩ :=
    lowerGuard test guardCore controlReg hw placement layout next flag s regular bounded
      matched avoids fresh rooted represented flagZero
  have bounded' : layout.Bounded (next + 2) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_add_right next 2)
  have avoidsTest : layout.Avoids next := by
    intro τ v i
    exact Nat.ne_of_lt (bounded v i)
  have guardRooted : afterGuard.locals.Rooted afterGuard.heap := test.env_rooted rooted
  obtain ⟨bodyPlacement, bodyTarget, bodyRun, bodyMatches, bodyArena, bodyAgrees, _⟩ :=
    bodyCore controlReg hw guardPlacement layout (next + 2) resultSlot flag guardTarget
      regular bounded' guardMatches avoids (Nat.lt_of_lt_of_le fresh (Nat.le_add_right next 2))
      resultFlag copySafe guardRooted guardArena preservedFlag
  have bodyTest : bodyTarget.regs next = 1 := by
    have preserved := lowerStmtCore_regs_eq (r := next) bodyRun.erase
      regular bounded' avoidsTest
      (Nat.lt_trans (Nat.lt_succ_self next) (Nat.lt_succ_self (next + 1)))
      (flag_not_mem_valueRegs result resultSlot next
        (Nat.le_trans resultFlag (Nat.le_of_lt fresh))) (Nat.ne_of_gt fresh)
    exact preserved.trans tested
  have bodyRooted : afterBody.locals.Rooted afterBody.heap := iteration.env_rooted guardRooted
  obtain ⟨finalPlacement, t, restRun, property, finalArena, restAgrees, finalMatches⟩ :=
    restCore controlReg hw bodyPlacement layout next resultSlot flag bodyTarget regular bounded
      bodyMatches.1 avoids fresh resultFlag copySafe bodyRooted bodyArena bodyMatches.2
  obtain ⟨tailSteps, restCount, tailRun⟩ :=
    ExecutionCost.drop_initialized_one restRun bodyTest
  have initialized : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign next (.const 1)) 2 s (s.setReg next 1) := .assign trivial
  have reset : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign (next + 1) (.const 0)) 2 (s.setReg next 1)
        ((s.setReg next 1).setReg (next + 1) 0) := .assign trivial
  have active : (s.setReg next 1).eval (.var next) ≠ 0 := by
    change (s.setReg next 1).regs next ≠ 0
    rw [Source.State.setReg_same]
    exact Word.one_ne_zero hw
  have conditionTrue : guardTarget.eval (.var next) ≠ 0 := by
    change guardTarget.regs next ≠ 0
    rw [tested]
    exact Word.one_ne_zero hw
  have returnCheck : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.ite (.var flag) (.assign next (.const 0)) .skip) 2 bodyTarget bodyTarget :=
    .iteFalse (c := .var flag) trivial bodyMatches.2 .skip
  have agreed : Placement.Agrees entry.heap placement finalPlacement :=
    guardAgrees.trans_of_shape
      (bodyAgrees.trans_of_shape restAgrees iteration.heap_shapeExtends) test.heap_shapeExtends
  refine ⟨finalPlacement, t, ?_, property, finalArena, agreed, finalMatches⟩
  convert Source.LocalMeasuredExec.seq initialized
    (Source.LocalMeasuredExec.whileTrue (c := .var next) trivial active
      (.seq reset (.seq guardRun
        (.iteTrue (c := .var next) trivial conditionTrue (.seq bodyRun returnCheck))))
      tailRun) using 1
  simp only [Expr.compile, List.length_singleton]
  omega

/-- A returning body retains both allocations and the actual returned value;
only the loop's private test register is cleared on exit. -/
theorem whileReturn
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {entry afterGuard finish : Complexity.Language.State Γ} {value : Value result}
    {cursor guardCursor finalCursor guardSteps bodySteps : Nat}
    (test : Complexity.Language.Exec program guard entry afterGuard (.returned true))
    (iteration : Complexity.Language.Exec program body afterGuard finish (.returned value))
    (guardCore : ArenaCoreSimulates test w heapLimit depth cursor guardCursor guardSteps)
    (bodyCore : ArenaCoreSimulates iteration w heapLimit depth guardCursor finalCursor bodySteps) :
    ArenaCoreSimulates (Complexity.Language.Exec.whileReturn test iteration)
      w heapLimit depth cursor finalCursor (guardSteps + bodySteps + 17) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched
    avoids fresh resultFlag copySafe rooted represented flagZero
  obtain ⟨guardPlacement, guardTarget, guardRun, guardMatches, guardArena, guardAgrees,
      tested, preservedFlag⟩ :=
    lowerGuard test guardCore controlReg hw placement layout next flag s regular bounded
      matched avoids fresh rooted represented flagZero
  have bounded' : layout.Bounded (next + 2) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (bounded v i) (Nat.le_add_right next 2)
  have avoidsTest : layout.Avoids next := by
    intro τ v i
    exact Nat.ne_of_lt (bounded v i)
  have guardRooted : afterGuard.locals.Rooted afterGuard.heap := test.env_rooted rooted
  obtain ⟨finalPlacement, bodyTarget, bodyRun, property, bodyArena, bodyAgrees, bodyLocals⟩ :=
    bodyCore controlReg hw guardPlacement layout (next + 2) resultSlot flag guardTarget
      regular bounded' guardMatches avoids (Nat.lt_of_lt_of_le fresh (Nat.le_add_right next 2))
      resultFlag copySafe guardRooted guardArena preservedFlag
  have initialized : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign next (.const 1)) 2 s (s.setReg next 1) := .assign trivial
  have reset : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign (next + 1) (.const 0)) 2 (s.setReg next 1)
        ((s.setReg next 1).setReg (next + 1) 0) := .assign trivial
  have active : (s.setReg next 1).eval (.var next) ≠ 0 := by
    change (s.setReg next 1).regs next ≠ 0
    rw [Source.State.setReg_same]
    exact Word.one_ne_zero hw
  have conditionTrue : guardTarget.eval (.var next) ≠ 0 := by
    change guardTarget.regs next ≠ 0
    rw [tested]
    exact Word.one_ne_zero hw
  have raised : bodyTarget.eval (.var flag) ≠ 0 := by
    change bodyTarget.regs flag ≠ 0
    rw [property.2]
    exact Word.one_ne_zero hw
  have clear : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (.assign next (.const 0)) 2 bodyTarget (bodyTarget.setReg next 0) := .assign trivial
  have cleared : (bodyTarget.setReg next 0).eval (.var next) = 0 :=
    Source.State.setReg_same _ _ _
  refine ⟨finalPlacement, bodyTarget.setReg next 0, ?_, ?_,
    bodyArena.setReg next 0, ?_, ?_⟩
  · convert Source.LocalMeasuredExec.seq initialized
      (Source.LocalMeasuredExec.whileTrue (c := .var next) trivial active
        (.seq reset (.seq guardRun
          (.iteTrue (c := .var next) trivial conditionTrue
            (.seq bodyRun (.iteTrue (c := .var flag) trivial raised clear)))))
        (.whileFalse (c := .var next) trivial cleared)) using 1
    simp only [Expr.compile, List.length_singleton]
    omega
  · refine ⟨?_, ?_⟩
    · rw [resultExprs_setReg_eval result resultSlot next 0 bodyTarget
        (flag_not_mem_valueRegs result resultSlot next
          (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))]
      exact property.1
    · exact (Source.State.setReg_ne bodyTarget next flag 0 (Nat.ne_of_lt fresh)).trans
        property.2
  · exact guardAgrees.trans_of_shape bodyAgrees test.heap_shapeExtends
  · intro separate τ v i
    exact RegisterMap.Matches.setReg_of_ne (bodyLocals separate) avoidsTest 0 v i

end ArenaCoreSimulates
end Ram.LanguageCompiler
