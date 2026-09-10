/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Layout
import Complexity.Computability.Ram.Memory.Arena.Registers
import Complexity.Computability.Ram.Memory.Arena.Scope
import Complexity.Computability.Ram.Source.Bounds

/-!
# Lowering typed programs with borrowed buffers to structured RAM code

The lowering is syntax-directed and independent of inputs, execution witnesses,
range proofs and cost bounds. Bindings receive fresh local slots for their
actual fields; Unit has no fields. Calls flatten typed arguments and receive
actual results using the existing calling convention. Buffer reads, writes and
slices emit ordinary address arithmetic and memory instructions. Successful
source access and realization justify safety; no runtime check is added here.
Allocation uses the shared arena cursor and the existing initialization loop;
its capacity, placement growth and behavior need allocation-aware simulation.
An allocation scope saves that cursor in one fresh local and restores it after
the body with an unconditional raw sequence, including after a source return.
Restoring metadata neither clears data nor changes the result fields or flag.

Each statement child is lowered once. An internal return flag records whether
the function returned; sequence tails and the final normal continuation inspect
that flag instead of copying the tail into every branch. The flag is a real
local word and its assignments and tests are emitted by the existing compiler.
It is separate from the result fields, including a Unit result's empty tuple.
Loops reevaluate their guard block on every iteration using a private Boolean
result and private guard-return flag. A body return retains the enclosing
function's flag and clears the loop test before the next loop condition.
Falling through a source function is not certified as a successful source
return. Behavioral transfer concerns executions that actually return.

Function-local bounds are inferred from the generated IR. No instruction cost
or source execution relation is defined here. Multi-field return copying is
sequential, not a hidden snapshot: its simulation requires the source layout to
avoid the result region. Generated function layouts reserve that region.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The actual word expressions for an atomic argument. Unit contributes no field. -/
def atomExprs (layout : RegisterMap Γ) (atom : Atom Γ τ) : List Expr :=
  List.ofFn (atomFieldExpr layout atom)

@[simp] theorem atomExprs_length (layout : RegisterMap Γ) (atom : Atom Γ τ) :
    (atomExprs layout atom).length = fieldCount τ := by
  simp only [atomExprs, List.length_ofFn]

/-- Flatten call operands in their declared order, omitting only Unit fields. -/
def argsExprs (layout : RegisterMap Γ) : {params : List Ty} → Args Γ params → List Expr
  | _, .nil => []
  | _, .cons atom rest => atomExprs layout atom ++ argsExprs layout rest

@[simp] theorem argsExprs_length (layout : RegisterMap Γ) (args : Args Γ params) :
    (argsExprs layout args).length = contextSize params := by
  induction args with
  | nil => rfl
  | cons atom rest ih => simp [argsExprs, contextSize, ih]

/-- Copy fields in order using real assignments. Every expression is evaluated
at its assignment; correctness needs preservation of later source fields.
The singleton form retains the ordinary scalar assignment without a trailing skip. -/
def copyFields (dst : Reg) : List Expr → Ram.Stmt
  | [] => .skip
  | [expr] => .assign dst expr
  | expr :: next :: rest =>
      .seq (.assign dst expr) (copyFields (dst + 1) (next :: rest))

/-- Materialize the primitive's actual fields, without a dummy Unit register.
Structured values copy their fields in order; buffer fields remain borrowed
descriptors rather than copies of the underlying storage. -/
def lowerPrim (layout : RegisterMap Γ) (dst : Reg) : {τ : Ty} → Prim Γ τ → Ram.Stmt
  | .nat, prim => .assign dst (primExpr layout prim .nat)
  | .bool, prim => .assign dst (primExpr layout prim .bool)
  | .unit, _ => .skip
  | .buffer _, prim => copyFields dst (primExprs layout prim)
  | .prod _ _, prim => copyFields dst (primExprs layout prim)
  | .option _, prim => copyFields dst (primExprs layout prim)

/-- Scalar assignments and empty Unit materialization are the corresponding
singleton and empty cases of the same ordered field-copy code. -/
theorem lowerPrim_eq_copyFields (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    lowerPrim layout dst prim = copyFields dst (primExprs layout prim) := by
  cases τ <;> cases prim <;> rfl

/-- Update an existing local through its actual field region. This reuses
primitive materialization, including real descriptor copies and empty Unit
updates; an assignment to the same buffer binding is not removed. -/
def lowerAssign (layout : RegisterMap Γ) (target : Var Γ τ) (value : Prim Γ τ) : Ram.Stmt :=
  lowerPrim layout (RegisterMap.base layout target) value

/-- Write the function's actual result fields. Multiple fields require a
non-overlapping source layout; the code does not provide an implicit snapshot. -/
def lowerReturn (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ) : Ram.Stmt :=
  copyFields resultSlot (atomExprs layout atom)

/-- Read one actual cell through the represented buffer base and source index. -/
def lowerRead (layout : RegisterMap Γ) (dst : Reg) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) : Ram.Stmt :=
  .assign dst (Expr.index (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩)
    (atomExpr layout index .nat))

/-- Write one actual cell; the source and realization premises justify the
address and cell representation instead of adding an uncounted bounds check. -/
def lowerWrite (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) : Ram.Stmt :=
  .store (.bin .add (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩)
    (atomExpr layout index .nat)) (atomExpr layout value (Scalar.cell kind))

/-- Construct the actual borrowed descriptor with address addition and a length
copy. Its caller allocates both destinations beyond the source layout. -/
def lowerSlice (layout : RegisterMap Γ) (dst : Reg) (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat) : Ram.Stmt :=
  .seq (.assign dst (.bin .add (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩)
    (atomExpr layout offset .nat))) (.assign (dst + 1) (atomExpr layout length .nat))

/-- Materialize both source operands before reserving and initializing storage.
The live source layout must lie below `next`. Scratch after the two returned
fields can be reused once initialization has completed. -/
def lowerAlloc {kind : CellTy} (layout : RegisterMap Γ) (next : Reg)
    (length : Atom Γ .nat) (initial : Atom Γ kind.toTy) : Ram.Stmt :=
  .seq (.assign (next + 1) (atomExpr layout length .nat))
    (.seq (.assign (next + 2) (atomExpr layout initial (Scalar.cell kind)))
      (Source.Arena.inlineRegisters next).allocate)

/-- Lower each source child once, with an initialized, separate return flag.
Calls restore the caller's flag before assigning their fresh result fields.
This internal lowering requires its register-separation invariants; `lowerStmt`
chooses the flag and initializes it automatically. -/
def lowerStmtCore {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg) :
    Complexity.Language.Stmt signatures Γ result → Ram.Stmt
  | .skip => .skip
  | .assign target value => lowerAssign layout target value
  | .letPrim (τ := τ) value body =>
      .seq (lowerPrim layout next value)
        (lowerStmtCore (RegisterMap.extend layout τ next)
          (next + fieldCount τ) resultSlot flag body)
  | .read (kind := kind) buffer index body =>
      .seq (lowerRead layout next buffer index)
        (lowerStmtCore (RegisterMap.extend layout kind.toTy next)
          (next + fieldCount kind.toTy) resultSlot flag body)
  | .write buffer index value => lowerWrite layout buffer index value
  | .slice (kind := kind) buffer offset length body =>
      .seq (lowerSlice layout next buffer offset length)
        (lowerStmtCore (RegisterMap.extend layout (.buffer kind) next)
          (next + fieldCount (.buffer kind)) resultSlot flag body)
  | .alloc (kind := kind) length initial body =>
      .seq (lowerAlloc layout next length initial)
        (lowerStmtCore (RegisterMap.extend layout (.buffer kind) next)
          (next + fieldCount (.buffer kind)) resultSlot flag body)
  | .scope body =>
      .seq (Source.Arena.Scope.capture next)
        (.seq (lowerStmtCore layout (next + 1) resultSlot flag body)
          (Source.Arena.Scope.release next))
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
  | .matchOption (τ := τ) value noneBranch someBranch =>
      .ite (optionTagExpr layout value)
        (.seq (copyFields next (optionPayloadExprs layout value))
          (lowerStmtCore (RegisterMap.extend layout τ next)
            (next + fieldCount τ) resultSlot flag someBranch))
        (lowerStmtCore layout next resultSlot flag noneBranch)
  | .while guard body =>
      .seq (.assign next (.const 1))
        (.while (.var next)
          (.seq (.assign (next + 1) (.const 0))
            (.seq (lowerStmtCore layout (next + 2) next (next + 1) guard)
              (.ite (.var next)
                (.seq (lowerStmtCore layout (next + 2) resultSlot flag body)
                  (.ite (.var flag) (.assign next (.const 0)) .skip))
                .skip))))
  | .ret value => .seq (lowerReturn layout resultSlot value) (.assign flag (.const 1))

/-- A scope reserves its one checkpoint slot in addition to the actual body
locals. Release uses that same slot and introduces no further source local. -/
theorem lowerStmtCore_scope_regBound {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (body : Complexity.Language.Stmt signatures Γ result) :
    (lowerStmtCore layout next resultSlot flag (.scope body)).regBound =
      max (next + 1) (lowerStmtCore layout (next + 1) resultSlot flag body).regBound := by
  change max (Source.Arena.Scope.capture next).regBound
    (max (lowerStmtCore layout (next + 1) resultSlot flag body).regBound
      (Source.Arena.Scope.release next).regBound) = _
  rw [Source.Arena.Scope.capture_regBound, Source.Arena.Scope.release_regBound,
    Nat.max_left_comm, Nat.max_self, Nat.max_comm]

/-- Evaluate a value-producing block without leaving the surrounding function.
Its result fields and private return flag follow the current live layout. A
block return ends this block only; its actual outer-local and heap updates remain
available to the enclosing computation. Successful evaluation must be proved. -/
def lowerBlock {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next : Reg)
    (block : Complexity.Language.Stmt signatures Γ result) : Ram.Stmt :=
  let flag := next + fieldCount result
  .seq (.assign flag (.const 0)) (lowerStmtCore layout (flag + 1) next flag block)

/-- Reserve the flag above live source slots and actual result fields. Unit
reserves no result word; the flag itself always performs real control work. -/
def returnFlag (result : Ty) (next resultSlot : Reg) : Reg :=
  max next (resultSlot + fieldCount result)

/-- Lower a statement and retain its normal continuation exactly once. The
fresh flag hides internal return bookkeeping from both the source program and
the public simulation's register hypotheses. Source returns bypass the tail.
The flag reservation alone does not separate an arbitrary source layout from
the result region: multi-field-copy safety is an explicit simulation premise. -/
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
  intro expr member
  change expr ∈ (valueRegs τ resultSlot).map Expr.var at member
  obtain ⟨slot, slotMember, rfl⟩ := List.mem_map.mp member
  exact (mem_valueRegs.mp slotMember).2

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
