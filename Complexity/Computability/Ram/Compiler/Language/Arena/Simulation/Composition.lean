/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues

/-!
# Sequential and conditional arena simulation

Sequential composition passes the first execution's actual placement, cursor
and shared state to the second execution. Source shape growth and rootedness
justify retaining the original descriptors across both placement extensions.
Returning from the first statement skips the second statement through the
existing compiled return-flag branch.

Conditionals execute the selected source branch with the same initial arena.
Option matching binds the actual payload only after its tag selects `some`;
leaving that binding retains the branch's current heap and outer locals.
The rules use existing measured RAM constructors and their actual field copies,
guard and jump instructions; no additional evaluator or cost table is used.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth cursor finalCursor steps : Nat} {Γ : List Ty} {result : Ty}
variable {entry finish : Complexity.Language.State Γ}

/-- Continue at the actual intermediate heap, cursor and placement after normal
completion. The generated return-flag check costs two instructions. -/
theorem seqNormal {first second : Complexity.Language.Stmt signatures Γ result}
    {middle : Complexity.Language.State Γ} {outcome : Control result}
    {head : Complexity.Language.Exec program first entry middle .normal}
    {tail : Complexity.Language.Exec program second middle finish outcome}
    {middleCursor firstSteps secondSteps : Nat}
    (firstSimulation : ArenaCoreSimulates head w heapLimit depth cursor middleCursor firstSteps)
    (secondSimulation :
      ArenaCoreSimulates tail w heapLimit depth middleCursor finalCursor secondSteps) :
    ArenaCoreSimulates (.seqNormal head tail) w heapLimit depth cursor finalCursor
      (firstSteps + 2 + secondSteps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨middlePlacement, middleTarget, firstRun, middleMatches, middleArena, firstAgrees, _⟩ :=
    firstSimulation controlReg hw placement layout next resultSlot flag s regular bounded
      matched avoids fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨finalPlacement, t, secondRun, property, finalArena, secondAgrees, finalMatches⟩ :=
    secondSimulation controlReg hw middlePlacement layout next resultSlot flag middleTarget
      regular bounded middleMatches.1 avoids fresh resultFlag copySafe
      (head.env_rooted rooted) middleArena middleMatches.2
  refine ⟨finalPlacement, t, ?_, property, finalArena,
    firstAgrees.trans_of_shape secondAgrees head.heap_shapeExtends, finalMatches⟩
  convert Source.LocalMeasuredExec.seq firstRun
    (Source.LocalMeasuredExec.iteFalse (c := .var flag) (yes := .skip)
      trivial middleMatches.2 secondRun) using 1
  simp only [Expr.compile, List.length_singleton]
  omega

/-- A returned first statement retains its final arena and skips the remaining
statement. The taken return-flag branch costs three instructions. -/
theorem seqReturn {first second : Complexity.Language.Stmt signatures Γ result}
    {value : Value result}
    {head : Complexity.Language.Exec program first entry finish (.returned value)}
    (simulation : ArenaCoreSimulates head w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.seqReturn (second := second) head) w heapLimit depth cursor finalCursor
      (steps + 3) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨finalPlacement, t, firstRun, property, finalArena, agreed, finalMatches⟩ :=
    simulation controlReg hw placement layout next resultSlot flag s regular bounded
      matched avoids fresh resultFlag copySafe rooted arena flagZero
  have raised : t.eval (.var flag) ≠ 0 := by
    change t.regs flag ≠ 0
    rw [property.2]
    exact Word.one_ne_zero hw
  exact ⟨finalPlacement, t,
    .seq firstRun (.iteTrue (c := .var flag) trivial raised .skip),
    property, finalArena, agreed, finalMatches⟩

/-- The true branch retains its actual final arena and pays for condition
evaluation, the conditional jump and the jump over the other branch. -/
theorem iteTrue {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {outcome : Control result}
    {test : condition.eval entry.locals = true}
    {body : Complexity.Language.Exec program yes entry finish outcome}
    (simulation : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.iteTrue (no := no) test body) w heapLimit depth cursor finalCursor
      (steps + 3) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨finalPlacement, t, executed, property, finalArena, agreed, finalMatches⟩ :=
    simulation controlReg hw placement layout next resultSlot flag s regular bounded
      matched avoids fresh resultFlag copySafe rooted arena flagZero
  have fits : Scalar.toNat .bool (condition.eval entry.locals) < 2 ^ w := by
    rw [test]
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  have decoded :=
    atomExpr_toNat layout condition .bool entry.locals s.regs s.mem hw matched fits
  have conditionTrue : s.eval (atomExpr layout condition .bool) ≠ 0 := by
    intro zero
    change (s.eval (atomExpr layout condition .bool)).toNat = _ at decoded
    rw [zero, test] at decoded
    exact Nat.zero_ne_one decoded
  refine ⟨finalPlacement, t, ?_, property, finalArena, agreed, finalMatches⟩
  convert Source.LocalMeasuredExec.iteTrue
    (atomExpr_readsBelow layout condition .bool s) conditionTrue executed using 1
  simp only [atomExpr_compile_length]
  omega

/-- The false branch retains its actual final arena and pays for condition
evaluation and the conditional jump. -/
theorem iteFalse {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {outcome : Control result}
    {test : condition.eval entry.locals = false}
    {body : Complexity.Language.Exec program no entry finish outcome}
    (simulation : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.iteFalse (yes := yes) test body) w heapLimit depth cursor finalCursor
      (steps + 2) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨finalPlacement, t, executed, property, finalArena, agreed, finalMatches⟩ :=
    simulation controlReg hw placement layout next resultSlot flag s regular bounded
      matched avoids fresh resultFlag copySafe rooted arena flagZero
  have fits : Scalar.toNat .bool (condition.eval entry.locals) < 2 ^ w := by
    rw [test]
    exact Nat.two_pow_pos w
  have decoded :=
    atomExpr_toNat layout condition .bool entry.locals s.regs s.mem hw matched fits
  have conditionFalse : s.eval (atomExpr layout condition .bool) = 0 := by
    apply (Word.toNat_eq_zero_iff _).mp
    simpa only [test, Scalar.toNat] using decoded
  refine ⟨finalPlacement, t, ?_, property, finalArena, agreed, finalMatches⟩
  convert Source.LocalMeasuredExec.iteFalse
    (atomExpr_readsBelow layout condition .bool s) conditionFalse executed using 1
  simp only [atomExpr_compile_length]
  omega

/-- The absent option selects the ordinary branch without manufacturing or
copying a payload. Its actual branch keeps its allocation effects. -/
theorem matchNone {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {outcome : Control result} {selected : value.eval entry.locals = none}
    {body : Complexity.Language.Exec program noneBranch entry finish outcome}
    (simulation : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.matchNone (someBranch := someBranch) selected body)
      w heapLimit depth cursor finalCursor (steps + 2) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨finalPlacement, t, executed, property, finalArena, agreed, finalMatches⟩ :=
    simulation controlReg hw placement layout next resultSlot flag s regular bounded
      matched avoids fresh resultFlag copySafe rooted arena flagZero
  have tested := optionTagExpr_eval_none layout value entry.locals s matched selected
  refine ⟨finalPlacement, t, ?_, property, finalArena, agreed, finalMatches⟩
  convert Source.LocalMeasuredExec.iteFalse
    (optionTagExpr_readsBelow layout value s) tested executed using 1
  simp only [optionTagExpr_compile_length]
  omega

/-- A present option copies its actual payload into fresh lexical fields before
executing its branch. Nested buffer roots are retained, and the final placement,
heap, outer-variable updates and control survive leaving the payload binding. -/
theorem matchSome {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {payload : Value τ} {finish : Complexity.Language.State (τ :: Γ)}
    {outcome : Control result} {selected : value.eval entry.locals = some payload}
    {body : Complexity.Language.Exec program someBranch
      (Complexity.Language.State.cons payload entry) finish outcome}
    (payloadFits : ValueFits w (τ := τ) payload)
    (simulation : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.matchSome (noneBranch := noneBranch) selected body)
      w heapLimit depth cursor finalCursor (2 * fieldCount τ + steps + 3) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  have first := copyOptionPayload_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout next value entry.locals s hw matched selected payloadFits bounded
  have matching : RegisterMap.Matches (RegisterMap.extend layout τ next) placement
      (Env.cons payload entry.locals)
      (s.setRegs (valueRegs τ next) (valueWords placement payload)).regs :=
    matched.setRegs bounded payload payloadFits
  have payloadRooted : ValueRooted entry.heap payload := by
    have optionRooted := value.eval_rooted rooted
    simpa only [selected, ValueRooted] using optionRooted
  have bodyRooted : (Env.cons payload entry.locals).Rooted entry.heap :=
    Env.Rooted.cons rooted payload payloadRooted
  have flagPreserved := (valueRegs_setRegs_other s τ next flag
    (valueWords placement payload)
    (flag_not_mem_valueRegs_of_lt τ next flag fresh)).trans flagZero
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    simulation controlReg hw placement (RegisterMap.extend layout τ next)
      (next + fieldCount τ) resultSlot flag _
      (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching
      (RegisterMap.Avoids.extend avoids fresh)
      (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
      (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
      bodyRooted (arena.setRegs _ _) flagPreserved
  have tested : s.eval (optionTagExpr layout value) ≠ 0 := by
    rw [optionTagExpr_eval_some layout value entry.locals s matched selected]
    exact Word.one_ne_zero hw
  refine ⟨finalPlacement, t, ?_, ControlMatches.tail property, finalArena, agreed, ?_⟩
  · convert Source.LocalMeasuredExec.iteTrue
      (optionTagExpr_readsBelow layout value s) tested (.seq first rest) using 1
    simp only [optionTagExpr_compile_length]
    omega
  · intro separate
    exact RegisterMap.Matches.tail (finalMatches (separate.extend
      (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

end Ram.LanguageCompiler.ArenaCoreSimulates
