/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Layout
import Complexity.Computability.Ram.Source.Bounds

/-!
# Lowering typed scalar programs to structured RAM code

The lowering is syntax-directed and independent of inputs, execution witnesses,
range proofs and cost bounds. Scalar bindings receive fresh local slots; Unit
bindings have no fields. Calls flatten the typed arguments and receive the
actual result fields using the existing calling convention.

Statements are lowered with a normal continuation. A return writes the fixed
function-result slot and discards that continuation, so a return nested in a
binding, branch or sequence bypasses the enclosing tail. Falling through a
source function is not certified as a successful source return by this syntax
construction. Behavioral transfer is a separate theorem about executions that
actually return.

Function-local bounds are inferred from the generated IR. No instruction cost
or source execution relation is defined here.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The actual word expressions for an atomic argument. Unit contributes no field. -/
def atomExprs (layout : RegisterMap Γ) : {τ : Ty} → Atom Γ τ → List Expr
  | .nat, atom => [atomExpr layout atom .nat]
  | .bool, atom => [atomExpr layout atom .bool]
  | .unit, _ => []

@[simp] theorem atomExprs_length (layout : RegisterMap Γ) (atom : Atom Γ τ) :
    (atomExprs layout atom).length = fieldCount τ := by
  cases τ <;> rfl

/-- Flatten call operands in their declared order, omitting only Unit fields. -/
def argsExprs (layout : RegisterMap Γ) : {params : List Ty} → Args Γ params → List Expr
  | _, .nil => []
  | _, .cons atom rest => atomExprs layout atom ++ argsExprs layout rest

@[simp] theorem argsExprs_length (layout : RegisterMap Γ) (args : Args Γ params) :
    (argsExprs layout args).length = contextSize params := by
  induction args with
  | nil => rfl
  | cons atom rest ih => simp [argsExprs, contextSize, ih]

/-- Materialize the primitive's actual result, without a dummy Unit register. -/
def lowerPrim (layout : RegisterMap Γ) (dst : Reg) : {τ : Ty} → Prim Γ τ → Ram.Stmt
  | .nat, prim => .assign dst (primExpr layout prim .nat)
  | .bool, prim => .assign dst (primExpr layout prim .bool)
  | .unit, _ => .skip

/-- Write the function's fixed result field. Unit has an empty result tuple. -/
def lowerReturn (layout : RegisterMap Γ) (resultSlot : Reg) :
    {τ : Ty} → Atom Γ τ → Ram.Stmt
  | .nat, atom => .assign resultSlot (atomExpr layout atom .nat)
  | .bool, atom => .assign resultSlot (atomExpr layout atom .bool)
  | .unit, _ => .skip

/-- Lower a statement with its normal continuation. Source returns discard it.
Fresh lexical slots can be reused after their scopes finish; caller registers
are restored by the existing function-call semantics. -/
def lowerStmt {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg) :
    Complexity.Language.Stmt signatures Γ result → Ram.Stmt → Ram.Stmt
  | .skip, continuation => continuation
  | .letPrim (τ := τ) value body, continuation =>
      .seq (lowerPrim layout next value)
        (lowerStmt (RegisterMap.extend layout τ next)
          (next + fieldCount τ) resultSlot body continuation)
  | .call fn args body, continuation =>
      .seq (.call (valueRegs signatures[fn].result next) fn.val (argsExprs layout args))
        (lowerStmt (RegisterMap.extend layout signatures[fn].result next)
          (next + fieldCount signatures[fn].result) resultSlot body continuation)
  | .seq first second, continuation =>
      lowerStmt layout next resultSlot first
        (lowerStmt layout next resultSlot second continuation)
  | .ite condition yes no, continuation =>
      .ite (atomExpr layout condition .bool)
        (lowerStmt layout next resultSlot yes continuation)
        (lowerStmt layout next resultSlot no continuation)
  | .ret value, _ => lowerReturn layout resultSlot value

/-- Read precisely the declared result fields after the lowered body finishes. -/
def resultExprs (τ : Ty) (resultSlot : Reg) : List Expr :=
  (valueRegs τ resultSlot).map Expr.var

@[simp] theorem resultExprs_length (τ : Ty) (resultSlot : Reg) :
    (resultExprs τ resultSlot).length = fieldCount τ := by
  simp only [resultExprs, List.length_map, valueRegs_length]

/-- Result expressions fit the reserved result tuple, independently of the body. -/
theorem resultExprs_bounded (τ : Ty) (resultSlot : Reg) :
    ∀ expr ∈ resultExprs τ resultSlot, expr.Bounded (resultSlot + fieldCount τ) := by
  cases τ <;> simp [resultExprs, valueRegs, fieldCount, Expr.Bounded]

/-- Parameters occupy the initial compact prefix, followed by the reserved
result fields and then fresh lexical slots. Only normal fallthrough reaches
the terminal skip; this does not claim that a missing source return succeeds. -/
def lowerBody {signatures : List Signature} (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) : Ram.Stmt :=
  lowerStmt (parameterMap signatures[fn].params)
    (contextSize signatures[fn].params + fieldCount signatures[fn].result)
    (contextSize signatures[fn].params) (program.body fn) .skip

/-- The actual lowered function, with its local frame inferred from its IR. -/
def lowerFunc {signatures : List Signature} (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) : Func where
  params := contextSize signatures[fn].params
  locals := max (contextSize signatures[fn].params + fieldCount signatures[fn].result)
    (lowerBody program fn).regBound
  body := lowerBody program fn
  results := resultExprs signatures[fn].result (contextSize signatures[fn].params)

@[simp] theorem lowerFunc_params {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerFunc program fn).params = contextSize signatures[fn].params := rfl

@[simp] theorem lowerFunc_body {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerFunc program fn).body = lowerBody program fn := rfl

@[simp] theorem lowerFunc_results_length {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerFunc program fn).results.length = fieldCount signatures[fn].result :=
  resultExprs_length _ _

/-- Static local operands, parameters and result fields fit the inferred frame.
Existence and arities of called functions are separate from this local property. -/
theorem lowerFunc_wellFormed {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerFunc program fn).WellFormed := by
  refine ⟨Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_left _ _),
    Ram.Stmt.wellFormed_of_regBound_le (Nat.le_max_right _ _), ?_⟩
  intro expr member
  exact (resultExprs_bounded _ _ expr member).mono (Nat.le_max_left _ _)

/-- Preserve the source signature order in the finite target function table. -/
def lowerProgram {signatures : List Signature} (program : Complexity.Language.Program signatures) :
    Ram.Program := List.ofFn (lowerFunc program)

@[simp] theorem lowerProgram_length {signatures : List Signature}
    (program : Complexity.Language.Program signatures) :
    (lowerProgram program).length = signatures.length := by
  simp [lowerProgram]

@[simp] theorem lowerProgram_getElem {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerProgram program)[fn.val]'(by simp [fn.isLt]) = lowerFunc program fn := by
  simp [lowerProgram]

/-- A typed source function index resolves to its actual lowered body. -/
@[simp] theorem lowerProgram_lookup {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerProgram program)[fn.val]? = some (lowerFunc program fn) := by
  simp [lowerProgram, fn.isLt]

/-- Every emitted function satisfies its inferred local-register bound. -/
theorem lowerProgram_wellFormed {signatures : List Signature}
    (program : Complexity.Language.Program signatures) :
    ∀ fn ∈ lowerProgram program, fn.WellFormed := by
  intro fn member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact lowerFunc_wellFormed program index

end Ram.LanguageCompiler
