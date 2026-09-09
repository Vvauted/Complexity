/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Layout
import Complexity.Language.Eval.Verification

/-!
# Source-level realization conditions for the word backend

`RealizedExec` retains the same successful finite source execution while recording
the mathematical value ranges and sufficient maximum call nesting used by the
word backend. Its depth parameter is a nesting capacity, not an instruction
budget: a call's continuation and sequential siblings reuse the caller's depth.

Erasure gives the independent `Complexity.Language.Exec`. No target execution,
register assignment or chosen instruction count occurs in these conditions.
Local assignment updates the actual lexical environment; buffer operations use
the actual shared heap.
Caller-local restoration never resets the callee's final heap. Buffer range
conditions concern lengths and actual scalar operands; physical placement and
address representation belong to the separate simulation layer.
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
  | write bufferFits indexFits valueFits written => exact .write written
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih => exact .slice sliced ih
  | seqNormal head tail ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn head ih => exact .seqReturn ih
  | iteTrue test body ih => exact .iteTrue test ih
  | iteFalse test body ih => exact .iteFalse test ih
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
  | write => trivial
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih => exact ih
  | seqNormal head tail ihHead ihTail => exact ihTail
  | seqReturn head ih => exact ih
  | iteTrue test body ih => exact ih
  | iteFalse test body ih => exact ih
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
  | write bufferFits indexFits valueFits written =>
      exact .write bufferFits indexFits valueFits written
  | slice bufferFits offsetFits lengthFits sliced viewFits body ih =>
      exact .slice bufferFits offsetFits lengthFits sliced viewFits (ih capacity)
  | seqNormal head tail ihHead ihTail => exact .seqNormal (ihHead capacity) (ihTail capacity)
  | seqReturn head ih => exact .seqReturn (ih capacity)
  | iteTrue test body ih => exact .iteTrue test (ih capacity)
  | iteFalse test body ih => exact .iteFalse test (ih capacity)
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

/-- Structural realization conditions with the source language's two successful
postconditions. The extra parameter records call capacity, not elapsed time. -/
def RealizationWP {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Complexity.Language.Program signatures) (w depth : Nat)
    (stmt : Complexity.Language.Stmt signatures Γ result)
    (normal : Complexity.Language.State Γ → Prop)
    (returned : Value result → Complexity.Language.State Γ → Prop)
    (entry : Complexity.Language.State Γ) : Prop :=
  ∃ finish control, RealizedExec program w depth stmt entry finish control ∧
    control.Satisfies normal returned finish

namespace RealizationWP

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Complexity.Language.Program signatures} {w depth : Nat}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {normal normal' : Complexity.Language.State Γ → Prop}
variable {returned returned' : Value result → Complexity.Language.State Γ → Prop}
variable {entry : Complexity.Language.State Γ}

/-- Erasing ranges and nesting gives total correctness of the same source node. -/
theorem erase (h : RealizationWP program w depth stmt normal returned entry) :
    Complexity.Language.TotalWP program stmt normal returned entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  exact ⟨finish, control, execution.erase, post⟩

/-- Weaken ordinary source postconditions while retaining realization. -/
theorem mono_post (h : RealizationWP program w depth stmt normal returned entry)
    (hnormal : ∀ finish, normal finish → normal' finish)
    (hreturned : ∀ value finish, returned value finish → returned' value finish) :
    RealizationWP program w depth stmt normal' returned' entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  refine ⟨finish, control, execution, ?_⟩
  cases control with
  | normal => exact hnormal finish post
  | returned value => exact hreturned value finish post
  | fault fault => exact post

/-- Increase the available nesting without changing source postconditions. -/
theorem mono_depth (h : RealizationWP program w depth stmt normal returned entry)
    {depth' : Nat} (capacity : depth ≤ depth') :
    RealizationWP program w depth' stmt normal returned entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  exact ⟨finish, control, execution.mono_depth capacity, post⟩

@[simp] theorem skip_iff :
    RealizationWP program w depth .skip normal returned entry ↔ normal entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .normal, .skip entry, post⟩

/-- Assignment requires the actual primitive to fit and continues with the
updated local, without imposing a time budget or changing the heap. -/
@[simp] theorem assign_iff {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ) :
    RealizationWP program w depth (.assign target value) normal returned entry ↔
      PrimFits w entry.locals value ∧ normal (entry.set target (value.eval entry.locals)) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | assign target value entry fits => exact ⟨fits, post⟩
  · rintro ⟨fits, post⟩
    exact ⟨_, .normal, .assign target value entry fits, post⟩

/-- Return materialization requires the actual source result to fit. -/
@[simp] theorem ret_iff (value : Atom Γ result) :
    RealizationWP program w depth (.ret value) normal returned entry ↔
      ValueFits w (value.eval entry.locals) ∧ returned (value.eval entry.locals) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | ret value entry fits => exact ⟨fits, post⟩
  · rintro ⟨fits, post⟩
    exact ⟨entry, .returned (value.eval entry.locals), .ret value entry fits, post⟩

/-- The primitive's range and the scoped continuation concern its actual value. -/
@[simp] theorem letPrim_iff {τ : Ty} (value : Prim Γ τ)
    (continuation : Complexity.Language.Stmt signatures (τ :: Γ) result) :
    RealizationWP program w depth (.letPrim value continuation) normal returned entry ↔
      PrimFits w entry.locals value ∧
        RealizationWP program w depth continuation (fun finish => normal finish.tail)
          (fun value finish => returned value finish.tail)
          (Complexity.Language.State.cons (value.eval entry.locals) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | letPrim fits body => exact ⟨fits, _, control, body, post⟩
  · rintro ⟨fits, finish, control, execution, post⟩
    exact ⟨finish.tail, control, .letPrim fits execution, post⟩

/-- A read binds the actual current-heap cell and its representation range. -/
@[simp] theorem read_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat)
    (continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result) :
    RealizationWP program w depth (.read buffer index continuation) normal returned entry ↔
      ValueFits w (buffer.eval entry.locals) ∧ index.eval entry.locals < 2 ^ w ∧
        ∃ value, entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value ∧
          ValueFits w (kind.toValue value) ∧
          RealizationWP program w depth continuation (fun finish => normal finish.tail)
            (fun value finish => returned value finish.tail)
            (Complexity.Language.State.cons (kind.toValue value) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | read bufferFits indexFits loaded valueFits body =>
        exact ⟨bufferFits, indexFits, _, loaded, valueFits, _, control, body, post⟩
  · rintro ⟨bufferFits, indexFits, value, loaded, valueFits, finish, control, body, post⟩
    exact ⟨finish.tail, control, .read bufferFits indexFits loaded valueFits body, post⟩

/-- A write exposes its actual updated shared heap, not a restored snapshot. -/
@[simp] theorem write_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) :
    RealizationWP program w depth (.write buffer index value) normal returned entry ↔
      ValueFits w (buffer.eval entry.locals) ∧ index.eval entry.locals < 2 ^ w ∧
        ValueFits w (value.eval entry.locals) ∧
        ∃ heap, entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
          (kind.ofValue (value.eval entry.locals)) = .ok heap ∧ normal ⟨entry.locals, heap⟩ := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | write bufferFits indexFits valueFits written =>
        exact ⟨bufferFits, indexFits, valueFits, _, written, post⟩
  · rintro ⟨bufferFits, indexFits, valueFits, heap, written, post⟩
    exact ⟨⟨entry.locals, heap⟩, .normal,
      .write bufferFits indexFits valueFits written, post⟩

/-- A slice retains its actual object identity and offset; range conditions do
not assign a physical address to that view. -/
@[simp] theorem slice_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat)
    (continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result) :
    RealizationWP program w depth (.slice buffer offset length continuation)
        normal returned entry ↔
      ValueFits w (buffer.eval entry.locals) ∧ offset.eval entry.locals < 2 ^ w ∧
        length.eval entry.locals < 2 ^ w ∧
        ∃ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
          (length.eval entry.locals) = .ok view ∧ ValueFits w (τ := .buffer kind) view ∧
          RealizationWP program w depth continuation (fun finish => normal finish.tail)
            (fun value finish => returned value finish.tail)
            (Complexity.Language.State.cons view entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | slice bufferFits offsetFits lengthFits sliced viewFits body =>
        exact ⟨bufferFits, offsetFits, lengthFits, _, sliced, viewFits, _, control, body, post⟩
  · rintro ⟨bufferFits, offsetFits, lengthFits, view, sliced, viewFits,
      finish, control, body, post⟩
    exact ⟨finish.tail, control,
      .slice bufferFits offsetFits lengthFits sliced viewFits body, post⟩

/-- Separate mathematical read success from the continuation's actual cell.
The latter may use both the successful read equation and the cell's range. -/
theorem read_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : index.eval entry.locals < 2 ^ w)
    (loaded : ∃ value, entry.heap.read (buffer.eval entry.locals)
      (index.eval entry.locals) = .ok value ∧ ValueFits w (kind.toValue value))
    (body : ∀ value, entry.heap.read (buffer.eval entry.locals)
      (index.eval entry.locals) = .ok value → ValueFits w (kind.toValue value) →
      RealizationWP program w depth continuation (fun finish => normal finish.tail)
        (fun value finish => returned value finish.tail)
        (Complexity.Language.State.cons (kind.toValue value) entry)) :
    RealizationWP program w depth (.read buffer index continuation) normal returned entry := by
  obtain ⟨value, found, fits⟩ := loaded
  exact (read_iff buffer index continuation).mpr
    ⟨bufferFits, indexFits, value, found, fits, body value found fits⟩

/-- Separate a successful source update from reasoning about its actual heap. -/
theorem write_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : index.eval entry.locals < 2 ^ w)
    (valueFits : ValueFits w (value.eval entry.locals))
    (written : ∃ heap, entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
      (kind.ofValue (value.eval entry.locals)) = .ok heap)
    (post : ∀ heap, entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
      (kind.ofValue (value.eval entry.locals)) = .ok heap → normal ⟨entry.locals, heap⟩) :
    RealizationWP program w depth (.write buffer index value) normal returned entry := by
  obtain ⟨heap, found⟩ := written
  exact (write_iff buffer index value).mpr
    ⟨bufferFits, indexFits, valueFits, heap, found, post heap found⟩

/-- A fitting relative extent identifies the actual sliced descriptor without
requiring users to choose an existential handle. -/
theorem slice_of_bound {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (offsetFits : offset.eval entry.locals < 2 ^ w)
    (lengthFits : length.eval entry.locals < 2 ^ w)
    (bound : offset.eval entry.locals + length.eval entry.locals ≤
      (buffer.eval entry.locals).length)
    (body : RealizationWP program w depth continuation (fun finish => normal finish.tail)
      (fun value finish => returned value finish.tail)
      (Complexity.Language.State.cons
        (τ := .buffer kind)
        ⟨(buffer.eval entry.locals).object,
          (buffer.eval entry.locals).offset + offset.eval entry.locals, length.eval entry.locals⟩
        entry)) :
    RealizationWP program w depth (.slice buffer offset length continuation)
      normal returned entry :=
  (slice_iff buffer offset length continuation).mpr
    ⟨bufferFits, offsetFits, lengthFits, _, Buffer.slice_eq _ bound, lengthFits, body⟩

/-- Sequential siblings reuse the same nesting capacity; returns skip the tail. -/
@[simp] theorem seq_iff (first second : Complexity.Language.Stmt signatures Γ result) :
    RealizationWP program w depth (.seq first second) normal returned entry ↔
      RealizationWP program w depth first
        (RealizationWP program w depth second normal returned) returned entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | seqNormal firstExec secondExec =>
        exact ⟨_, .normal, firstExec, finish, control, secondExec, post⟩
    | seqReturn firstExec => exact ⟨_, _, firstExec, post⟩
  · rintro ⟨middle, control, execution, post⟩
    cases control with
    | normal =>
        obtain ⟨finish, control, next, post⟩ := post
        exact ⟨finish, control, .seqNormal execution next, post⟩
    | returned value => exact ⟨middle, .returned value, .seqReturn execution, post⟩
    | fault fault => exact False.elim post

/-- Only the selected source branch must satisfy operation ranges. -/
@[simp] theorem ite_iff (condition : Atom Γ .bool)
    (yes no : Complexity.Language.Stmt signatures Γ result) :
    RealizationWP program w depth (.ite condition yes no) normal returned entry ↔
      if condition.eval entry.locals then RealizationWP program w depth yes normal returned entry
      else RealizationWP program w depth no normal returned entry := by
  cases hcondition : condition.eval entry.locals with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => cases hcondition.symm.trans truth
        | iteFalse truth body => exact ⟨finish, control, body, post⟩
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteFalse hcondition execution, post⟩
  | true =>
      simp only [↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => exact ⟨finish, control, body, post⟩
        | iteFalse truth body => cases hcondition.symm.trans truth
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteTrue hcondition execution, post⟩

/-- Unfold one actual loop round. The guard must return a Boolean, and its final
state feeds either the exit postcondition or the body. A normal body continues
the same loop from its own final state; a returned value exits the enclosing
function. This equation is not a simplification rule for recursive unfolding. -/
theorem while_iff (guard : Complexity.Language.Stmt signatures Γ .bool)
    (body : Complexity.Language.Stmt signatures Γ result) :
    RealizationWP program w depth (.while guard body) normal returned entry ↔
      RealizationWP program w depth guard (fun _ => False)
        (fun test afterGuard => if test then
          RealizationWP program w depth body
            (RealizationWP program w depth (.while guard body) normal returned)
            returned afterGuard
          else normal afterGuard) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | whileFalse test => exact ⟨finish, .returned false, test, post⟩
    | whileTrue test iteration rest =>
        exact ⟨_, .returned true, test, _, .normal, iteration, finish, control, rest, post⟩
    | whileReturn test iteration =>
        exact ⟨_, .returned true, test, finish, _, iteration, post⟩
  · rintro ⟨afterGuard, guardControl, test, post⟩
    cases guardControl with
    | normal => exact False.elim post
    | fault error => exact False.elim post
    | returned decision =>
        cases decision with
        | false => exact ⟨afterGuard, .normal, .whileFalse test, post⟩
        | true =>
            obtain ⟨afterBody, bodyControl, iteration, post⟩ := post
            cases bodyControl with
            | normal =>
                obtain ⟨finish, control, rest, post⟩ := post
                exact ⟨finish, control, .whileTrue test iteration rest, post⟩
            | returned value => exact ⟨afterBody, .returned value, .whileReturn test iteration, post⟩
            | fault error => exact False.elim post

/-- Prove realizability and termination by descent across complete guard/body
rounds. The invariant holds at the next guard entry, not necessarily after an
effectful guard. False guards and early returns need no descent. The relation is
mathematical termination evidence, separate from instruction costs and nesting. -/
theorem while_wellFounded {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    {r : Complexity.Language.State Γ → Complexity.Language.State Γ → Prop}
    (wf : WellFounded r)
    (step : ∀ current, invariant current →
      RealizationWP program w depth guard (fun _ => False)
        (fun test afterGuard => if test then
          RealizationWP program w depth body
            (fun afterBody => invariant afterBody ∧ r afterBody current)
            returned afterGuard
          else normal afterGuard) current)
    (initial : invariant entry) :
    RealizationWP program w depth (.while guard body) normal returned entry := by
  revert initial
  induction entry using wf.induction with
  | h current ih =>
      intro initial
      apply (while_iff guard body).mpr
      refine (step current initial).mono_post (fun _ impossible => impossible) ?_
      intro test afterGuard post
      cases test with
      | false => exact post
      | true =>
          exact post.mono_post (fun afterBody property => ih afterBody property.2 property.1)
            (fun _ _ property => property)

/-- A natural-valued variant is a special case of mathematical round descent,
not an instruction budget or execution fuel. Operation ranges and the shared
call-nesting capacity remain in the same realization judgment. -/
theorem while_variant {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    (variant : Complexity.Language.State Γ → Nat)
    (step : ∀ current, invariant current →
      RealizationWP program w depth guard (fun _ => False)
        (fun test afterGuard => if test then
          RealizationWP program w depth body
            (fun afterBody => invariant afterBody ∧ variant afterBody < variant current)
            returned afterGuard
          else normal afterGuard) current)
    (initial : invariant entry) :
    RealizationWP program w depth (.while guard body) normal returned entry :=
  while_wellFounded (measure variant).wf step initial

end RealizationWP

/-- A function's source-level admissibility conditions suffice for its actual
successful execution with the selected value ranges and call capacity. The
mathematical behavior remains in the independent source `FunctionTotal`. -/
def FunctionRealizable {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w depth : Nat)
    (fn : Fin signatures.length) (pre : Env signatures[fn].params → Heap → Prop) : Prop :=
  ∀ args heap, pre args heap → ∃ finish value,
    RealizedExec program w depth (program.body fn) ⟨args, heap⟩ finish (.returned value)

namespace FunctionRealizable

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w depth : Nat} {fn : Fin signatures.length}
variable {pre pre' : Env signatures[fn].params → Heap → Prop}

/-- Structural range proofs must reach a real return, not a missing-return fault. -/
theorem of_wp (body : ∀ args heap, pre args heap →
    RealizationWP program w depth (program.body fn) (fun _ => False)
      (fun _ _ => True) ⟨args, heap⟩) : FunctionRealizable program w depth fn pre := by
  intro args heap hpre
  obtain ⟨finish, control, execution, post⟩ := body args heap hpre
  cases control with
  | normal => exact False.elim post
  | returned value => exact ⟨finish, value, execution⟩
  | fault fault => exact False.elim post

/-- Existing function realizability supplies the same returned source invocation. -/
theorem wp (h : FunctionRealizable program w depth fn pre)
    (args : Env signatures[fn].params) (heap : Heap) (hpre : pre args heap) :
    RealizationWP program w depth (program.body fn) (fun _ => False)
      (fun _ _ => True) ⟨args, heap⟩ := by
  obtain ⟨finish, value, execution⟩ := h args heap hpre
  exact ⟨finish, .returned value, execution, trivial⟩

/-- A stronger admissibility predicate preserves realizability. -/
theorem consequence (h : FunctionRealizable program w depth fn pre)
    (input : ∀ args heap, pre' args heap → pre args heap) :
    FunctionRealizable program w depth fn pre' :=
  fun args heap hpre => h args heap (input args heap hpre)

/-- More permitted nesting preserves the same source implementation. -/
theorem mono_depth (h : FunctionRealizable program w depth fn pre)
    {depth' : Nat} (capacity : depth ≤ depth') :
    FunctionRealizable program w depth' fn pre := by
  intro args heap hpre
  obtain ⟨finish, value, execution⟩ := h args heap hpre
  exact ⟨finish, value, execution.mono_depth capacity⟩

end FunctionRealizable

namespace RealizationWP

/-- Reuse a separately proved mathematical contract at the actual callee return.
Only the subsequent operation ranges and nesting remain to be established;
the algorithm's result property is not reproved during realization. -/
theorem call {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {w depth calleeDepth : Nat}
    {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    {feasible pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (realizable : FunctionRealizable program w calleeDepth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (arguments : EnvFits w (args.eval entry.locals)) (nesting : calleeDepth + 1 ≤ depth)
    (hfeasible : feasible (args.eval entry.locals) entry.heap)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value finalHeap, post (args.eval entry.locals) entry.heap value finalHeap →
      ValueFits w value →
      RealizationWP program w depth continuation (fun finish => normal finish.tail)
        (fun result finish => returned result finish.tail)
        (Complexity.Language.State.cons value ⟨entry.locals, finalHeap⟩)) :
    RealizationWP program w depth (.call fn args continuation) normal returned entry := by
  obtain ⟨calleeFinish, value, invocation⟩ :=
    realizable (args.eval entry.locals) entry.heap hfeasible
  have property := specification.postcondition hpre invocation.erase
  obtain ⟨finish, control, execution, result⟩ :=
    body value calleeFinish.heap property invocation.returned_fits
  cases depth with
  | zero => omega
  | succ depth =>
      exact ⟨finish.tail, control,
        .callReturn arguments
          (invocation.mono_depth (Nat.le_of_succ_le_succ nesting)) execution, result⟩

/-- Reuse an ordinary equation for this callee invocation directly. The existing
call rule transports the proved value; the caller only establishes realization
of its continuation using the actual returned value's range. -/
theorem call_of_eval {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Complexity.Language.Program signatures} {w depth calleeDepth : Nat}
    {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : Complexity.Language.State Γ → Prop}
    {returned : Value result → Complexity.Language.State Γ → Prop}
    {entry : Complexity.Language.State Γ}
    {feasible : Env signatures[fn].params → Heap → Prop}
    {value : Value signatures[fn].result} {finalHeap : Heap}
    (realizable : FunctionRealizable program w calleeDepth fn feasible)
    (evaluated : program.eval fn (args.eval entry.locals) entry.heap =
      Part.some (.ok value, finalHeap))
    (arguments : EnvFits w (args.eval entry.locals)) (nesting : calleeDepth + 1 ≤ depth)
    (hfeasible : feasible (args.eval entry.locals) entry.heap)
    (body : ValueFits w value →
      RealizationWP program w depth continuation (fun finish => normal finish.tail)
        (fun result finish => returned result finish.tail)
        (Complexity.Language.State.cons value ⟨entry.locals, finalHeap⟩)) :
    RealizationWP program w depth (.call fn args continuation) normal returned entry := by
  have specification : FunctionTotal program fn
      (fun actual initial => actual = args.eval entry.locals ∧ initial = entry.heap)
      (fun _ _ returned resultHeap => returned = value ∧ resultHeap = finalHeap) := by
    apply FunctionTotal.iff_eval.mpr
    rintro actual initial ⟨rfl, rfl⟩
    exact ⟨value, finalHeap, evaluated, rfl, rfl⟩
  apply call realizable specification arguments nesting hfeasible ⟨rfl, rfl⟩
  rintro actual actualHeap ⟨rfl, rfl⟩ fits
  exact body fits

end RealizationWP

end Ram.LanguageCompiler
