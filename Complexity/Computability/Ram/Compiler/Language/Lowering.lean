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

Each statement child is lowered once. An internal return flag records whether
the function returned; sequence tails and the final normal continuation inspect
that flag instead of copying the tail into every branch. The flag is a real
local word and its assignments and tests are emitted by the existing compiler.
It is separate from the result fields, including a Unit result's empty tuple.
Falling through a source function is not certified as a successful source
return. Behavioral transfer concerns executions that actually return.

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

/-- Lower each source child once, with an initialized, separate return flag.
Calls restore the caller's flag before assigning their fresh result fields.
This internal lowering requires its register-separation invariants; `lowerStmt`
chooses the flag and initializes it automatically. -/
def lowerStmtCore {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg) :
    Complexity.Language.Stmt signatures Γ result → Ram.Stmt
  | .skip => .skip
  | .letPrim (τ := τ) value body =>
      .seq (lowerPrim layout next value)
        (lowerStmtCore (RegisterMap.extend layout τ next)
          (next + fieldCount τ) resultSlot flag body)
  | .call fn args body =>
      .seq (.call (valueRegs signatures[fn].result next) fn.val (argsExprs layout args))
        (lowerStmtCore (RegisterMap.extend layout signatures[fn].result next)
          (next + fieldCount signatures[fn].result) resultSlot flag body)
  | .seq first second =>
      .seq (lowerStmtCore layout next resultSlot flag first)
        (.ite (.var flag) .skip (lowerStmtCore layout next resultSlot flag second))
  | .ite condition yes no =>
      .ite (atomExpr layout condition .bool)
        (lowerStmtCore layout next resultSlot flag yes)
        (lowerStmtCore layout next resultSlot flag no)
  | .ret value => .seq (lowerReturn layout resultSlot value) (.assign flag (.const 1))

/-- Reserve the flag above live source slots and actual result fields. Unit
reserves no result word; the flag itself always performs real control work. -/
def returnFlag (result : Ty) (next resultSlot : Reg) : Reg :=
  max next (resultSlot + fieldCount result)

/-- Lower a statement and retain its normal continuation exactly once. The
fresh flag hides internal return bookkeeping from both the source program and
the public simulation's register hypotheses. Source returns bypass the tail. -/
def lowerStmt {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) (continuation : Ram.Stmt) : Ram.Stmt :=
  let flag := returnFlag result next resultSlot
  .seq (.assign flag (.const 0))
    (.seq (lowerStmtCore layout (flag + 1) resultSlot flag stmt)
      (.ite (.var flag) .skip continuation))

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
result fields, private return flag and fresh lexical slots. A function has no
normal continuation to dispatch: initialize the flag and run its core directly.
This does not claim that a missing source return succeeds. -/
def lowerBody {signatures : List Signature} (program : Complexity.Language.Program signatures)
    (fn : Fin signatures.length) : Ram.Stmt :=
  let resultSlot := contextSize signatures[fn].params
  let next := resultSlot + fieldCount signatures[fn].result
  let flag := returnFlag signatures[fn].result next resultSlot
  .seq (.assign flag (.const 0))
    (lowerStmtCore (parameterMap signatures[fn].params) (flag + 1) resultSlot flag
      (program.body fn))

/-- Omitting the empty final dispatch does not change the inferred register
bound: the return flag is already named by its initialization. -/
theorem lowerBody_regBound_eq_lowerStmt {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerBody program fn).regBound =
      (lowerStmt (parameterMap signatures[fn].params)
        (contextSize signatures[fn].params + fieldCount signatures[fn].result)
        (contextSize signatures[fn].params) (program.body fn) .skip).regBound := by
  simp only [lowerBody, lowerStmt, Ram.Stmt.regBound, Expr.varBound,
    Nat.max_self, Nat.max_comm]
  rw [← Nat.max_assoc, Nat.max_self]

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
