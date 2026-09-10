/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Compiler.Language.Arena.Lowering
import Complexity.Computability.Ram.Compiler.Local.Function

/-!
# Static validity of lowered high-level programs

Typed source calls determine existing function indices and exact argument and
result arities. The lowering preserves these facts through every statement and
normal continuation. The maximum inferred local frame supplies the backend's
reserved-register boundary, including the actual function-entry trampoline.

`compile_eq_some` proves that the existing checked compiler accepts the generated
program without a user-supplied register or lookup proof. It establishes static
compilation only: source behavior, word representability and sufficient runtime
heap/stack space require their separate semantic proofs.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Sequential field materialization introduces no function call. -/
theorem copyFields_callsValid (program : Ram.Program) (dst : Reg) (fields : List Expr) :
    Compiler.CallsValid program (copyFields dst fields) := by
  induction fields generalizing dst with
  | nil => trivial
  | cons expr rest ih =>
      cases rest with
      | nil => trivial
      | cons next rest => exact ⟨trivial, ih (dst + 1)⟩

/-- Primitive materialization introduces no function call. -/
theorem lowerPrim_callsValid (program : Ram.Program) (layout : RegisterMap Γ)
    (dst : Reg) (prim : Prim Γ τ) : Compiler.CallsValid program (lowerPrim layout dst prim) := by
  cases τ with
  | nat | bool | unit => trivial
  | buffer kind =>
      cases prim with
      | atom atom => exact copyFields_callsValid program dst (atomExprs layout atom)

/-- Updating an existing local introduces no function call. -/
theorem lowerAssign_callsValid (program : Ram.Program) (layout : RegisterMap Γ)
    (target : Var Γ τ) (value : Prim Γ τ) :
    Compiler.CallsValid program (lowerAssign layout target value) :=
  lowerPrim_callsValid program layout (RegisterMap.base layout target) value

/-- Returning the declared fields introduces no function call. -/
theorem lowerReturn_callsValid (program : Ram.Program) (layout : RegisterMap Γ)
    (dst : Reg) (atom : Atom Γ τ) : Compiler.CallsValid program (lowerReturn layout dst atom) :=
  copyFields_callsValid program dst (atomExprs layout atom)

/-- Every typed source call has exactly the generated callee's field counts. -/
theorem call_callsValid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (layout : RegisterMap Γ)
    (fn : Fin signatures.length) (args : Args Γ signatures[fn].params) (dst : Reg) :
    Compiler.CallsValid (lowerProgram program)
      (.call (valueRegs signatures[fn].result dst) fn.val (argsExprs layout args)) := by
  apply Compiler.CallsValid.call_iff.mpr
  exact ⟨lowerFunc program fn, lowerProgram_lookup program fn,
    argsExprs_length layout args, by simp only [valueRegs_length, lowerFunc_results_length]⟩

/-- Every core call retains its typed argument and result arities. Return-flag
assignments and guards add no function references. -/
theorem lowerStmtCore_callsValid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) :
    Compiler.CallsValid (lowerProgram program)
      (lowerStmtCore layout next resultSlot flag stmt) := by
  induction stmt generalizing next resultSlot flag with
  | skip => trivial
  | assign target value => exact lowerAssign_callsValid _ layout target value
  | letPrim value body ih =>
      exact ⟨lowerPrim_callsValid _ _ _ _, ih _ _ _ _⟩
  | read buffer index body ih => exact ⟨trivial, ih _ _ _ _⟩
  | write buffer index value => trivial
  | slice buffer offset length body ih => exact ⟨⟨trivial, trivial⟩, ih _ _ _ _⟩
  | alloc length initial body ih => exact ⟨lowerAlloc_callsValid _ _ _ _ _, ih _ _ _ _⟩
  | scope body ih => exact ⟨trivial, ih _ _ _ _, trivial⟩
  | call fn args body ih =>
      exact ⟨call_callsValid program layout fn args next, ih _ _ _ _⟩
  | seq first second ihFirst ihSecond =>
      exact ⟨ihFirst _ _ _ _, trivial, ihSecond _ _ _ _⟩
  | ite condition yes no ihYes ihNo =>
      exact ⟨ihYes _ _ _ _, ihNo _ _ _ _⟩
  | «while» guard body ihGuard ihBody =>
      exact ⟨trivial, trivial, ihGuard _ _ _ _, ⟨ihBody _ _ _ _, trivial, trivial⟩, trivial⟩
  | ret value => exact ⟨lowerReturn_callsValid _ _ _ _, trivial⟩

/-- A call-valid normal continuation stays call-valid under syntax-directed
lowering. The return flag prevents a returned path from executing the tail. -/
theorem lowerStmt_callsValid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) (continuation : Ram.Stmt)
    (tailValid : Compiler.CallsValid (lowerProgram program) continuation) :
    Compiler.CallsValid (lowerProgram program)
      (lowerStmt layout next resultSlot stmt continuation) := by
  exact ⟨trivial, lowerStmtCore_callsValid program _ _ _ _ _, trivial, tailValid⟩

/-- All calls in a lowered function body resolve in the generated table. -/
theorem lowerBody_callsValid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    Compiler.CallsValid (lowerProgram program) (lowerBody program fn) :=
  ⟨trivial, lowerStmtCore_callsValid program _ _ _ _ _⟩

/-- The finite generated table satisfies the same check recursively at every body. -/
theorem lowerProgram_callsValid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) :
    ∀ f ∈ lowerProgram program, Compiler.CallsValid (lowerProgram program) f.body := by
  intro f member
  obtain ⟨fn, rfl⟩ := List.mem_ofFn.mp member
  exact lowerBody_callsValid program fn

/-- The reserved-register boundary covers all inferred local frames. One slot
also covers the scalar entry trampoline when the source program has no locals. -/
def programControl {signatures : List Signature}
    (program : Complexity.Language.Program signatures) : Nat :=
  max 1 ((lowerProgram program).foldr (fun f bound => max f.locals bound) 0)

theorem one_le_programControl {signatures : List Signature}
    (program : Complexity.Language.Program signatures) : 1 ≤ programControl program :=
  Nat.le_max_left _ _

/-- The selected global boundary covers each actual generated local frame. -/
theorem lowerFunc_locals_le_programControl {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerFunc program fn).locals ≤ programControl program := by
  have frames : ∀ functions : Ram.Program, ∀ f ∈ functions,
      f.locals ≤ functions.foldr (fun g bound => max g.locals bound) 0 := by
    intro functions
    induction functions with
    | nil => simp
    | cons g functions ih =>
        intro f member
        rcases List.mem_cons.mp member with rfl | member
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (ih f member) (Nat.le_max_right _ _)
  have member : lowerFunc program fn ∈ lowerProgram program :=
    List.mem_ofFn.mpr ⟨fn, rfl⟩
  exact Nat.le_trans (frames _ _ member) (Nat.le_max_right _ _)

/-- Runtime parameter registers fit without an additional caller layout. -/
theorem lowerFunc_params_le_programControl {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    contextSize signatures[fn].params ≤ programControl program :=
  Nat.le_trans (lowerFunc_wellFormed program fn).1 (lowerFunc_locals_le_programControl program fn)

/-- The complete result tuple fits the global boundary through its actual
reserved region in the generated local frame. -/
theorem lowerFunc_resultFields_le_programControl {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    fieldCount signatures[fn].result ≤ programControl program := by
  have withinFrame : fieldCount signatures[fn].result ≤ (lowerFunc program fn).locals :=
    Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_left _ _)
  exact Nat.le_trans withinFrame (lowerFunc_locals_le_programControl program fn)

/-- The existing function-entry trampoline and entire generated table satisfy
the checked linker's static conditions. No input or execution is used here. -/
theorem function_trampoline_valid {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    LocalCompiler.Valid (programControl program) (lowerProgram program)
      (LocalCompiler.Function.trampoline fn.val (contextSize signatures[fn].params)
        (fieldCount signatures[fn].result)) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro dst member
      exact Nat.lt_of_lt_of_le (List.mem_range.mp member)
        (lowerFunc_resultFields_le_programControl program fn)
    · intro expr member
      change expr ∈ (List.range (contextSize signatures[fn].params)).map Expr.var at member
      obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp member
      exact Nat.lt_of_lt_of_le (List.mem_range.mp inRange)
        (lowerFunc_params_le_programControl program fn)
  · apply Compiler.CallsValid.call_iff.mpr
    refine ⟨lowerFunc program fn, lowerProgram_lookup program fn, ?_, ?_⟩
    · simp only [LocalCompiler.Function.arguments, List.length_map, List.length_range,
        lowerFunc_params]
    · simp only [List.length_range, lowerFunc_results_length]
  · intro f member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    refine ⟨lowerFunc_wellFormed program index,
      lowerFunc_locals_le_programControl program index, lowerBody_callsValid program index, ?_⟩
    rw [lowerFunc_results_length]
    exact Nat.le_trans (Nat.sub_le _ _) (lowerFunc_resultFields_le_programControl program index)

/-- The existing linker output for a fixed source declaration and function.
No runtime argument, correctness proof or budget specializes this code. -/
def lowerCode {signatures : List Signature} (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) : Code :=
  LocalCompiler.rawLink (programControl program) (lowerProgram program)
    (LocalCompiler.Function.trampoline fn.val (contextSize signatures[fn].params)
      (fieldCount signatures[fn].result))

/-- Static checked compilation succeeds for the actual lowered function entry.
This is not a termination theorem or a word/stack-capacity certificate. -/
theorem compile_eq_some {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    LocalCompiler.Function.compile (programControl program) (lowerProgram program) fn.val
      (contextSize signatures[fn].params) = some (lowerCode program fn) := by
  unfold LocalCompiler.Function.compile
  rw [LocalCompiler.Function.resultArity_lookup (lowerProgram_lookup program fn),
    lowerFunc_results_length]
  exact LocalCompiler.compileChecked_some_iff.mpr ⟨function_trampoline_valid program fn, rfl⟩

end Ram.LanguageCompiler
