/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Compiler.Local.Basic

/-!
# Exact size of typed value and buffer lowering

The structural formulas below equal the length of the actual emitted machine
code. Every statement child contributes once, including both sides of a branch;
the normal continuation is not copied. Call sites retain the existing ABI's
argument and callee-frame expansion. Thus the formulas exclude exponential
continuation duplication without pretending that a call's code size is constant
when the callee's frame size varies.

These are static code lengths, not elapsed time. An execution selects branches
and can call the same function repeatedly. Runtime bounds require the separate
cost interpretation over that same execution.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Number of instructions materializing the primitive and assigning its fields.
`lowerPrim_stmtSize` derives this formula from the existing expression compiler. -/
def primCodeSize {Γ : List Ty} {τ : Ty} : Prim Γ τ → Nat
  | .atom _ => 2 * fieldCount τ
  | .add .. | .mul .. | .div .. | .mod .. | .eq .. | .lt .. | .le .. => 4
  | .sub .. => 8
  | .length _ => 2

/-- Emitted buffer-read length, justified by `lowerRead_stmtSize`. -/
def readCodeSize : Nat := 5

/-- Emitted buffer-write length, justified by `lowerWrite_stmtSize`. -/
def writeCodeSize : Nat := 5

/-- Emitted descriptor-construction length, justified by `lowerSlice_stmtSize`. -/
def sliceCodeSize : Nat := 6

/-- Exact static size after lowering, with each child counted once. The locals
table is the existing backend's actual callee-frame table, not a price chosen
by a program author. It is specialized to the generated table at function entry. -/
def sourceCodeSize {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (localsTable : Nat → Nat) : Complexity.Language.Stmt signatures Γ result → Nat
  | .skip => 0
  | .assign _ value => primCodeSize value
  | .letPrim value body => primCodeSize value + sourceCodeSize localsTable body
  | .read _ _ body => readCodeSize + sourceCodeSize localsTable body
  | .write .. => writeCodeSize
  | .slice _ _ _ body => sliceCodeSize + sourceCodeSize localsTable body
  | .call fn _ body =>
      2 * contextSize signatures[fn].params + 4 * localsTable fn.val + 5 +
        fieldCount signatures[fn].result + sourceCodeSize localsTable body
  | .seq first second => sourceCodeSize localsTable first + sourceCodeSize localsTable second + 3
  | .ite _ yes no => sourceCodeSize localsTable yes + sourceCodeSize localsTable no + 3
  | .while guard body => sourceCodeSize localsTable guard + sourceCodeSize localsTable body + 15
  | .ret _ => 2 * fieldCount result + 2

/-- Each atomic argument field is materialized by one actual instruction. -/
theorem atomExprs_compile_lengths (layout : RegisterMap Γ) (atom : Atom Γ τ) (dst : Reg) :
    ((atomExprs layout atom).map (fun expr => (expr.compile dst).length)).sum = fieldCount τ := by
  have materialized :
      (atomExprs layout atom).map (fun expr => (expr.compile dst).length) =
        (atomExprs layout atom).map (fun _ => 1) := by
    apply List.map_congr_left
    intro expr member
    change expr ∈ List.ofFn (atomFieldExpr layout atom) at member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact atomFieldExpr_compile_length layout atom i dst
  rw [materialized]
  simp only [List.map_const', List.sum_replicate_nat, atomExprs_length, Nat.mul_one]

/-- Flattened argument fields retain their exact materialization length. -/
theorem argsExprs_compile_lengths (layout : RegisterMap Γ) (args : Args Γ params) (dst : Reg) :
    ((argsExprs layout args).map (fun expr => (expr.compile dst).length)).sum = contextSize params := by
  induction args with
  | nil => rfl
  | cons atom rest ih =>
      simp only [argsExprs, List.map_append, List.sum_append,
        atomExprs_compile_lengths, ih, contextSize]

/-- Ordered copying charges each expression and its actual destination move. -/
theorem copyFields_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (dst : Reg) (fields : List Expr) :
    LocalCompiler.stmtSize control localsTable (copyFields dst fields) =
      (fields.map (fun expr => (expr.compile (ABI.scratch control)).length)).sum +
        fields.length := by
  induction fields generalizing dst with
  | nil => rfl
  | cons expr rest ih =>
      cases rest with
      | nil => simp [copyFields]
      | cons next rest =>
          simp only [copyFields, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
            ih, List.map_cons, List.sum_cons, List.length_cons]
          omega

/-- Primitive size is derived from emitted assignments and expression code. -/
theorem lowerPrim_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    LocalCompiler.stmtSize control localsTable (lowerPrim layout dst prim) = primCodeSize prim := by
  cases τ <;> cases prim <;>
    simp [lowerPrim, LocalCompiler.stmtSize_assign, LocalCompiler.stmtSize_skip,
      copyFields_stmtSize, atomExprs_compile_lengths, primExpr_compile_length, primCodeSize]

/-- Local assignment emits the same primitive materialization at the existing
binding's field region, with no additional control or snapshot instructions. -/
theorem lowerAssign_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (target : Var Γ τ) (value : Prim Γ τ) :
    LocalCompiler.stmtSize control localsTable (lowerAssign layout target value) =
      primCodeSize value :=
  lowerPrim_stmtSize control localsTable layout (RegisterMap.base layout target) value

/-- Every return field is materialized before setting the separate flag. -/
theorem lowerReturn_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (dst : Reg) (atom : Atom Γ τ) :
    LocalCompiler.stmtSize control localsTable (lowerReturn layout dst atom) = 2 * fieldCount τ := by
  rw [lowerReturn, copyFields_stmtSize, atomExprs_compile_lengths, atomExprs_length]
  omega

/-- A read charges base/index materialization, address addition, load and assignment. -/
theorem lowerRead_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (dst : Reg) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) :
    LocalCompiler.stmtSize control localsTable (lowerRead layout dst buffer index) =
      readCodeSize := by
  simp only [lowerRead, LocalCompiler.stmtSize_assign, Expr.index, Expr.compile,
    List.length_append, List.length_singleton, atomFieldExpr_compile_length,
    atomExpr_compile_length, readCodeSize]

/-- A write charges the actual address, cell materialization and store. -/
theorem lowerWrite_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) :
    LocalCompiler.stmtSize control localsTable (lowerWrite layout buffer index value) =
      writeCodeSize := by
  simp only [lowerWrite, LocalCompiler.stmtSize, LocalCompiler.compileStmt, Expr.compile,
    List.length_append, List.length_singleton, atomFieldExpr_compile_length,
    atomExpr_compile_length, writeCodeSize]

/-- A slice performs real base-address addition and a second descriptor-field copy. -/
theorem lowerSlice_stmtSize (control : Nat) (localsTable : Nat → Nat)
    (layout : RegisterMap Γ) (dst : Reg) (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat) :
    LocalCompiler.stmtSize control localsTable (lowerSlice layout dst buffer offset length) =
      sliceCodeSize := by
  simp only [lowerSlice, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
    Expr.compile, List.length_append, List.length_singleton, atomFieldExpr_compile_length,
    atomExpr_compile_length, sliceCodeSize]

/-- Actual call code includes argument materialization, frame work and receivers. -/
theorem lowerCall_stmtSize {signatures : List Signature}
    (control : Nat) (localsTable : Nat → Nat) (layout : RegisterMap Γ)
    (fn : Fin signatures.length) (args : Args Γ signatures[fn].params) (dst : Reg) :
    LocalCompiler.stmtSize control localsTable
        (.call (valueRegs signatures[fn].result dst) fn.val (argsExprs layout args)) =
      2 * contextSize signatures[fn].params + 4 * localsTable fn.val + 5 +
        fieldCount signatures[fn].result := by
  rw [LocalCompiler.stmtSize_call, ABI.callPrefixLocals_length_eq,
    argsExprs_compile_lengths, argsExprs_length, valueRegs_length]
  omega

/-- Every child in the core contributes once to actual emitted machine code.
The equation is uniform over register placement, word width and execution. -/
theorem lowerStmtCore_stmtSize {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (control : Nat) (localsTable : Nat → Nat) (layout : RegisterMap Γ)
    (next resultSlot flag : Reg) (stmt : Complexity.Language.Stmt signatures Γ result) :
    LocalCompiler.stmtSize control localsTable
        (lowerStmtCore layout next resultSlot flag stmt) = sourceCodeSize localsTable stmt := by
  induction stmt generalizing next resultSlot flag with
  | skip => rfl
  | assign target value => exact lowerAssign_stmtSize control localsTable layout target value
  | letPrim value body ih =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, lowerPrim_stmtSize,
        ih, sourceCodeSize]
  | read buffer index body ih =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, lowerRead_stmtSize,
        ih, sourceCodeSize]
  | write buffer index value => exact lowerWrite_stmtSize control localsTable layout _ _ _
  | slice buffer offset length body ih =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, lowerSlice_stmtSize,
        ih, sourceCodeSize]
  | call fn args body ih =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, lowerCall_stmtSize,
        ih, sourceCodeSize]
  | seq first second ihFirst ihSecond =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_ite,
        LocalCompiler.stmtSize_skip, Expr.compile, List.length_singleton,
        ihFirst, ihSecond, sourceCodeSize]
      omega
  | ite condition yes no ihYes ihNo =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_ite, atomExpr_compile_length,
        ihYes, ihNo, sourceCodeSize]
      omega
  | «while» guard body ihGuard ihBody =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
        LocalCompiler.stmtSize_while, LocalCompiler.stmtSize_ite, LocalCompiler.stmtSize_skip,
        Expr.compile, List.length_singleton, ihGuard, ihBody, sourceCodeSize]
      omega
  | ret value =>
      simp only [lowerStmtCore, LocalCompiler.stmtSize_seq, lowerReturn_stmtSize,
        LocalCompiler.stmtSize_assign, Expr.compile, List.length_singleton, sourceCodeSize]

/-- The wrapper adds flag initialization and a final dispatch, with exactly
one copy of the external continuation. These five instructions are not free. -/
theorem lowerStmt_stmtSize {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (control : Nat) (localsTable : Nat → Nat) (layout : RegisterMap Γ)
    (next resultSlot : Reg) (stmt : Complexity.Language.Stmt signatures Γ result)
    (continuation : Ram.Stmt) :
    LocalCompiler.stmtSize control localsTable (lowerStmt layout next resultSlot stmt continuation) =
      sourceCodeSize localsTable stmt + LocalCompiler.stmtSize control localsTable continuation + 5 := by
  simp only [lowerStmt, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
    LocalCompiler.stmtSize_ite, LocalCompiler.stmtSize_skip, lowerStmtCore_stmtSize,
    Expr.compile, List.length_singleton]
  omega

/-- A generated function body uses the actual generated callee-frame table. -/
theorem lowerBody_stmtSize {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (control : Nat) :
    LocalCompiler.stmtSize control (LocalCompiler.calleeLocals (lowerProgram program))
      (lowerBody program fn) =
      sourceCodeSize (LocalCompiler.calleeLocals (lowerProgram program)) (program.body fn) + 2 := by
  simp only [lowerBody, LocalCompiler.stmtSize_seq, LocalCompiler.stmtSize_assign,
    Expr.compile, List.length_singleton, lowerStmtCore_stmtSize]
  omega

/-- The specialized function exit removes exactly three instructions from the
generic wrapper with an empty normal continuation. -/
theorem lowerBody_stmtSize_add_three {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (control : Nat) :
    LocalCompiler.stmtSize control (LocalCompiler.calleeLocals (lowerProgram program))
        (lowerBody program fn) + 3 =
      LocalCompiler.stmtSize control (LocalCompiler.calleeLocals (lowerProgram program))
        (lowerStmt (parameterMap signatures[fn].params)
          (contextSize signatures[fn].params + fieldCount signatures[fn].result)
          (contextSize signatures[fn].params) (program.body fn) .skip) := by
  simp only [lowerBody_stmtSize, lowerStmt_stmtSize, LocalCompiler.stmtSize_skip]

end Ram.LanguageCompiler
