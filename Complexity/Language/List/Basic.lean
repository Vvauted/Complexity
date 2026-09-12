/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List
import Complexity.Language.RepresentedFunction

/-!
# Testing whether a represented linked list is empty

`List.IsEmpty.body` is an actual source statement: it matches the optional root
and returns a Boolean. It reads no node, allocates nothing and retains the
complete source state. The ordinary `List.isEmpty` contract follows from the
same root's existing linked-list representation, not from a host callback or
another list implementation.

The body is independent of its surrounding function table and the scalar cell
kind. The single-entry program makes it callable through the existing function
and linking interfaces. Machine representation and instruction counting remain
separate compiler obligations.
-/

namespace Complexity.Language.List.IsEmpty

/-- One optional linked root is the sole argument; the result is a Boolean. -/
def signature (kind : CellTy) : Signature :=
  ⟨[.option (.node kind)], .bool⟩

/-- Test the existing option tag without reading the node or following its tail. -/
def body (kind : CellTy) {signatures : List Signature} :
    Stmt signatures [.option (.node kind)] .bool :=
  .matchOption (.var .here) (.ret (.bool true)) (.ret (.bool false))

/-- The same source body as one callable entry, with no external function calls. -/
def program (kind : CellTy) : Program [signature kind] where
  body fn := Fin.cases (body kind) (fun index => Fin.elim0 index) fn

/-- The sole actual source function in this table. -/
def entry (kind : CellTy) : Fin [signature kind].length :=
  ⟨0, Nat.zero_lt_one⟩

@[simp] theorem program_body (kind : CellTy) :
    (program kind).body (entry kind) = body kind := rfl

/-- The tag test returns its actual Boolean and preserves every local and the
entire heap. Even an invalid nonempty handle requires no heap lookup here. -/
theorem body_exec {signatures : List Signature} (program : Program signatures)
    (kind : CellTy) (initial : State [.option (.node kind)]) :
    Exec program (body kind) initial initial (.returned initial.locals.head.isNone) := by
  cases selected : initial.locals.head with
  | none =>
      exact .matchNone selected (.ret (.bool true) initial)
  | some ref =>
      simpa only [State.tail_cons] using
        (Exec.matchSome (program := program) (value := .var .here)
          (noneBranch := .ret (.bool true)) (entry := initial) (payload := ref) selected
          (.ret (.bool false) (State.cons ref initial)))

/-- Every actual representation returns the ordinary list emptiness test.
The final heap is exactly the initial heap, not merely a shape extension. -/
theorem total (kind : CellTy) (values : List (CellValue kind)) :
    FunctionTotal (program kind) (entry kind)
      (fun args heap => (Representation.list kind).Rel values args.head heap)
      (fun _ initial value finish => value = values.isEmpty ∧ finish = initial) := by
  intro args heap observed
  have result : args.head.isNone = values.isEmpty := by
    change NodeRef.Contents heap args.head values at observed
    generalize root_eq : args.head = root at observed ⊢
    cases observed <;> rfl
  have executed := body_exec (program kind) kind ⟨args, heap⟩
  change Exec (program kind) (body kind) ⟨args, heap⟩ ⟨args, heap⟩
    (.returned args.head.isNone) at executed
  rw [result] at executed
  exact ⟨⟨args, heap⟩, values.isEmpty, executed, rfl, rfl⟩

/-- Ordinary linked-list input and Boolean output observations at the actual heaps. -/
def representation (kind : CellTy) :
    FunctionRepresentation (List (CellValue kind)) (fun _ => Bool) (signature kind) :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.single (Representation.list kind)) (fun _ => Representation.bool)

/-- The callable implementation refines the existing Lean `List.isEmpty` function.
The stronger exact-heap frame remains available in `total`. -/
theorem refines (kind : CellTy) :
    RepresentedFunction.Refines (program kind) (entry kind) (representation kind)
      (fun _ => True) (fun values => values.isEmpty) := by
  intro values _
  apply (total kind values).consequence (fun _ _ observed => observed)
  intro args initial value finish _ result
  change values.isEmpty = value
  exact result.1.symm

end Complexity.Language.List.IsEmpty
