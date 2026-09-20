/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization.Basic
import Complexity.Language.Verification

/-!
# Structural realization rules

`RealizationWP` combines successful source execution with word ranges, call-depth
capacity and normal/returned postconditions. Its structural rules preserve the
actual lexical environment and shared heap; they require no instruction budget.

Loop rules are in `Realization.Loop`; function contracts and call composition
are in `Realization.Function`.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

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

/-- Reading an immutable node binds its actual payload and shared tail. Only
the returned fields need numerical ranges; source object identifiers are not
machine addresses and are not required to fit a word. -/
@[simp] theorem readNode_iff {kind : CellTy} (ref : Atom Γ (.node kind))
    (continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result) :
    RealizationWP program w depth (.readNode ref continuation) normal returned entry ↔
      ∃ head tail, entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) ∧
        ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) ∧
        RealizationWP program w depth continuation (fun finish => normal finish.tail)
          (fun value finish => returned value finish.tail)
          (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
            (kind.toValue head, tail) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | readNode found valueFits body =>
        exact ⟨_, _, found, valueFits, _, control, body, post⟩
  · rintro ⟨head, tail, found, valueFits, finish, control, body, post⟩
    exact ⟨finish.tail, control, .readNode found valueFits body, post⟩

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

/-- Introduce the actual node payload, shared tail and their word ranges in the
continuation. The lookup success is retained as a hypothesis, not recomputed by
the compiled operation. -/
theorem readNode_of_success {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    (loaded : ∃ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) ∧
        ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail))
    (body : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
        ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) →
        RealizationWP program w depth continuation (fun finish => normal finish.tail)
          (fun value finish => returned value finish.tail)
          (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
            (kind.toValue head, tail) entry)) :
    RealizationWP program w depth (.readNode ref continuation) normal returned entry := by
  obtain ⟨head, tail, found, fits⟩ := loaded
  exact (readNode_iff ref continuation).mpr
    ⟨head, tail, found, fits, body head tail found fits⟩

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

/-- Matching an option requires only the selected branch. The payload range is
checked on its actual value; leaving the branch discards only its local binder. -/
@[simp] theorem matchOption_iff {τ : Ty} (value : Atom Γ (.option τ))
    (noneBranch : Complexity.Language.Stmt signatures Γ result)
    (someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result) :
    RealizationWP program w depth (.matchOption value noneBranch someBranch)
        normal returned entry ↔
      match value.eval entry.locals with
      | none => RealizationWP program w depth noneBranch normal returned entry
      | some payload => ValueFits w (τ := τ) payload ∧
          RealizationWP program w depth someBranch (fun finish => normal finish.tail)
            (fun result finish => returned result finish.tail)
            (Complexity.Language.State.cons payload entry) := by
  cases selected : value.eval entry.locals with
  | none =>
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | matchNone _ body => exact ⟨finish, control, body, post⟩
        | matchSome same _ body => cases selected.symm.trans same
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .matchNone selected execution, post⟩
  | some payload =>
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | matchNone same body => cases selected.symm.trans same
        | matchSome same fits body =>
            cases Option.some.inj (selected.symm.trans same)
            exact ⟨fits, _, control, body, post⟩
      · rintro ⟨fits, finish, control, execution, post⟩
        exact ⟨finish.tail, control, .matchSome selected fits execution, post⟩

end RealizationWP

end Ram.LanguageCompiler
