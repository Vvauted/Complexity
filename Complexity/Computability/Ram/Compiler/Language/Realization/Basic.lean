/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Layout
import Complexity.Language.Semantics

/-!
# Realized source executions

`RealizedExec` records the word ranges and sufficient call nesting of the same
successful finite source execution. Call depth is a capacity, not an instruction
budget: sequential statements and a call's continuation reuse it.

Erasure, outcome ranges and depth monotonicity do not mention target registers,
physical placement or chosen instruction costs. Heap effects and lexical updates
remain those of the independent source semantics.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A successful source execution whose actual operations fit the selected word
width and whose nested calls fit a given capacity. -/
inductive RealizedExec {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w : Nat) :
    Nat → {Γ : List Ty} → {result : Ty} → Complexity.Language.Stmt signatures Γ result →
      Complexity.Language.State Γ → Complexity.Language.State Γ → Control result → Prop where
  | skip {Γ : List Ty} {result : Ty} {depth : Nat} (entry : Complexity.Language.State Γ) :
      RealizedExec program w depth
        (.skip : Complexity.Language.Stmt signatures Γ result) entry entry .normal
  | assign {Γ : List Ty} {τ result : Ty} {depth : Nat}
      (target : Var Γ τ) (value : Prim Γ τ) (entry : Complexity.Language.State Γ)
      (fits : PrimFits w entry.locals value) :
      RealizedExec program w depth
        (.assign target value : Complexity.Language.Stmt signatures Γ result)
        entry (entry.set target (value.eval entry.locals)) .normal
  | letPrim {Γ : List Ty} {τ result : Ty} {depth : Nat} {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
      {control : Control result}
      (fits : PrimFits w entry.locals value)
      (body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (value.eval entry.locals) entry) finish control) :
      RealizedExec program w depth (.letPrim value continuation) entry finish.tail control
  | read {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (kind.toTy :: Γ)} {control : Control result}
      {value : CellValue kind}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (indexFits : index.eval entry.locals < 2 ^ w)
      (loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value)
      (valueFits : ValueFits w (kind.toValue value))
      (body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) finish control) :
      RealizedExec program w depth (.read buffer index continuation) entry finish.tail control
  | readNode {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {ref : Atom Γ (.node kind)}
      {continuation : Complexity.Language.Stmt signatures
        (.prod kind.toTy (.option (.node kind)) :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.prod kind.toTy (.option (.node kind)) :: Γ)}
      {control : Control result} {head : CellValue kind} {tail : Option (NodeRef kind)}
      (found : entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail))
      (valueFits : ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail))
      (body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) entry) finish control) :
      RealizedExec program w depth (.readNode ref continuation) entry finish.tail control
  | write {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : Complexity.Language.State Γ} {heap : Heap}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (indexFits : index.eval entry.locals < 2 ^ w)
      (valueFits : ValueFits w (value.eval entry.locals))
      (written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap) :
      RealizedExec program w depth (.write buffer index value :
        Complexity.Language.Stmt signatures Γ result) entry ⟨entry.locals, heap⟩ .normal
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy} {depth : Nat}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)} {control : Control result}
      {view : Buffer kind}
      (bufferFits : ValueFits w (buffer.eval entry.locals))
      (offsetFits : offset.eval entry.locals < 2 ^ w)
      (lengthFits : length.eval entry.locals < 2 ^ w)
      (sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view)
      (viewFits : ValueFits w (τ := .buffer kind) view)
      (body : RealizedExec program w depth continuation
        (Complexity.Language.State.cons view entry) finish control) :
      RealizedExec program w depth (.slice buffer offset length continuation)
        entry finish.tail control
  | seqNormal {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Complexity.Language.State Γ} {control : Control result}
      (head : RealizedExec program w depth first entry middle .normal)
      (tail : RealizedExec program w depth second middle finish control) :
      RealizedExec program w depth (.seq first second) entry finish control
  | seqReturn {Γ : List Ty} {result : Ty} {depth : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {value : Value result}
      (head : RealizedExec program w depth first entry finish (.returned value)) :
      RealizedExec program w depth (.seq first second) entry finish (.returned value)
  | iteTrue {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (test : condition.eval entry.locals = true)
      (body : RealizedExec program w depth yes entry finish control) :
      RealizedExec program w depth (.ite condition yes no) entry finish control
  | iteFalse {Γ : List Ty} {result : Ty} {depth : Nat} {condition : Atom Γ .bool}
      {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (test : condition.eval entry.locals = false)
      (body : RealizedExec program w depth no entry finish control) :
      RealizedExec program w depth (.ite condition yes no) entry finish control
  | matchNone {Γ : List Ty} {result τ : Ty} {depth : Nat}
      {value : Atom Γ (.option τ)}
      {noneBranch : Complexity.Language.Stmt signatures Γ result}
      {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      (selected : value.eval entry.locals = none)
      (body : RealizedExec program w depth noneBranch entry finish control) :
      RealizedExec program w depth (.matchOption value noneBranch someBranch) entry finish control
  | matchSome {Γ : List Ty} {result τ : Ty} {depth : Nat}
      {value : Atom Γ (.option τ)}
      {noneBranch : Complexity.Language.Stmt signatures Γ result}
      {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {payload : Value τ}
      {finish : Complexity.Language.State (τ :: Γ)} {control : Control result}
      (selected : value.eval entry.locals = some payload)
      (payloadFits : ValueFits w (τ := τ) payload)
      (body : RealizedExec program w depth someBranch
        (Complexity.Language.State.cons payload entry) finish control) :
      RealizedExec program w depth (.matchOption value noneBranch someBranch)
        entry finish.tail control
  | whileFalse {Γ : List Ty} {result : Ty} {depth : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ}
      (test : RealizedExec program w depth guard entry finish (.returned false)) :
      RealizedExec program w depth (.while guard body) entry finish .normal
  | whileTrue {Γ : List Ty} {result : Ty} {depth : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard afterBody finish : Complexity.Language.State Γ} {control : Control result}
      (test : RealizedExec program w depth guard entry afterGuard (.returned true))
      (iteration : RealizedExec program w depth body afterGuard afterBody .normal)
      (rest : RealizedExec program w depth (.while guard body) afterBody finish control) :
      RealizedExec program w depth (.while guard body) entry finish control
  | whileReturn {Γ : List Ty} {result : Ty} {depth : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard finish : Complexity.Language.State Γ} {value : Value result}
      (test : RealizedExec program w depth guard entry afterGuard (.returned true))
      (iteration : RealizedExec program w depth body afterGuard finish (.returned value)) :
      RealizedExec program w depth (.while guard body) entry finish (.returned value)
  | ret {Γ : List Ty} {result : Ty} {depth : Nat}
      (value : Atom Γ result) (entry : Complexity.Language.State Γ)
      (fits : ValueFits w (value.eval entry.locals)) :
      RealizedExec program w depth (.ret value) entry entry (.returned (value.eval entry.locals))
  | callReturn {Γ : List Ty} {result : Ty} {depth : Nat} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {calleeFinish : Complexity.Language.State signatures[fn].params}
      {value : Value signatures[fn].result}
      {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
      {control : Control result}
      (arguments : EnvFits w (args.eval entry.locals))
      (callee : RealizedExec program w depth (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value))
      (body : RealizedExec program w (depth + 1) continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control) :
      RealizedExec program w (depth + 1) (.call fn args continuation) entry finish.tail control

/-- A successful control outcome carries either no value or a representable
returned value. This predicate depends on the outcome, never its execution proof. -/
def ControlFits (w : Nat) {result : Ty} (control : Control result) : Prop :=
  match control with
  | .normal => True
  | .returned value => ValueFits w value
  | .fault _ => False

namespace RealizedExec

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth : Nat} {Γ : List Ty} {result : Ty}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry finish : Complexity.Language.State Γ} {control : Control result}

/-- Realization certifies the same independent source execution. -/
theorem erase (execution : RealizedExec program w depth stmt entry finish control) :
    Complexity.Language.Exec program stmt entry finish control := by
  induction execution with
  | skip entry => exact .skip entry
  | assign target value entry fits => exact .assign target value entry
  | letPrim fits body ih => exact .letPrim ih
  | read bufferFits indexFits loaded valueFits body ih => exact .read loaded ih
  | readNode found valueFits body ih => exact .readNode found ih
  | write bufferFits indexFits valueFits written => exact .write written
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih => exact .slice sliced ih
  | seqNormal head tail ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn head ih => exact .seqReturn ih
  | iteTrue test body ih => exact .iteTrue test ih
  | iteFalse test body ih => exact .iteFalse test ih
  | matchNone selected body ih => exact .matchNone selected ih
  | matchSome selected payloadFits body ih => exact .matchSome selected ih
  | whileFalse test ih => exact .whileFalse ih
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact .whileTrue ihTest ihIteration ihRest
  | whileReturn test iteration ihTest ihIteration => exact .whileReturn ihTest ihIteration
  | ret value entry fits => exact .ret value entry
  | callReturn arguments callee body ihCallee ihBody => exact .callReturn ihCallee ihBody

/-- Source blocks with no local assignments retain the enclosing environment.
This does not assert unchanged heap contents or prohibit callee-local updates. -/
theorem locals_eq (execution : RealizedExec program w depth stmt entry finish control)
    (unchanged : stmt.NoLocalWrites) : finish.locals = entry.locals :=
  execution.erase.locals_eq unchanged

/-- Every actual returned value is representable; successful normal continuation
requires no result value, and a realized execution cannot fault. -/
theorem outcome_fits (execution : RealizedExec program w depth stmt entry finish control) :
    ControlFits w control := by
  induction execution with
  | skip => trivial
  | assign => trivial
  | letPrim fits body ih => exact ih
  | read bufferFits indexFits loaded valueFits body ih => exact ih
  | readNode found valueFits body ih => exact ih
  | write => trivial
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih => exact ih
  | seqNormal head tail ihHead ihTail => exact ihTail
  | seqReturn head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
  | matchNone selected body ih => exact ih
  | matchSome selected payloadFits body ih => exact ih
  | whileFalse => trivial
  | whileTrue test iteration rest ihTest ihIteration ihRest => exact ihRest
  | whileReturn test iteration ihTest ihIteration => exact ihIteration
  | ret value entry fits => exact fits
  | callReturn arguments callee body ihCallee ihBody => exact ihBody

/-- A caller may use the actual returned value's representation range. -/
theorem returned_fits {value : Value result}
    (execution : RealizedExec program w depth stmt entry finish (.returned value)) :
    ValueFits w value := execution.outcome_fits

/-- More allowed call nesting preserves the same execution and values. This
does not add instructions or change the word-range conditions. -/
theorem mono_depth (execution : RealizedExec program w depth stmt entry finish control)
    {depth' : Nat} (capacity : depth ≤ depth') :
    RealizedExec program w depth' stmt entry finish control := by
  induction execution generalizing depth' with
  | skip entry => exact .skip entry
  | assign target value entry fits => exact .assign target value entry fits
  | letPrim fits body ih => exact .letPrim fits (ih capacity)
  | read bufferFits indexFits loaded valueFits body ih =>
      exact .read bufferFits indexFits loaded valueFits (ih capacity)
  | readNode found valueFits body ih => exact .readNode found valueFits (ih capacity)
  | write bufferFits indexFits valueFits written =>
      exact .write bufferFits indexFits valueFits written
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih =>
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih capacity)
  | seqNormal head tail ihHead ihTail => exact .seqNormal (ihHead capacity) (ihTail capacity)
  | seqReturn head ih => exact .seqReturn (ih capacity)
  | iteTrue test body ih => exact .iteTrue test (ih capacity)
  | iteFalse test body ih => exact .iteFalse test (ih capacity)
  | matchNone selected body ih => exact .matchNone selected (ih capacity)
  | matchSome selected payloadFits body ih => exact .matchSome selected payloadFits (ih capacity)
  | whileFalse test ih => exact .whileFalse (ih capacity)
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      exact .whileTrue (ihTest capacity) (ihIteration capacity) (ihRest capacity)
  | whileReturn test iteration ihTest ihIteration =>
      exact .whileReturn (ihTest capacity) (ihIteration capacity)
  | ret value entry fits => exact .ret value entry fits
  | callReturn arguments callee body ihCallee ihBody =>
      cases depth' with
      | zero => omega
      | succ depth' =>
          exact .callReturn arguments
            (ihCallee (Nat.le_of_succ_le_succ capacity)) (ihBody capacity)

end RealizedExec

end Ram.LanguageCompiler
