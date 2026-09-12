/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List
import Complexity.Language.RepresentedFunction

/-!
# One-step decomposition of represented linked lists

`List.Uncons.body` matches the actual optional root. An absent root returns
`none`; a present root executes `Stmt.readNode` and returns the stored head and
identical tail reference. It neither traverses nor copies the tail, allocates
storage, or substitutes a mathematical list for the runtime lookup.

The source contract uses ordinary `List.head?` and `List.tail`, observed through
the existing product, option and linked-list representations at the unchanged
heap. Nat and Bool payloads share the same source body and proof. A valid list
observation supplies the actual typed lookup; arbitrary nonempty handles are
not silently treated as empty lists.
-/

namespace Complexity.Language.List.Uncons

/-- Decompose one optional node into its head and shared optional tail. -/
def signature (kind : CellTy) : Signature :=
  ⟨[.option (.node kind)], .option (.prod kind.toTy (.option (.node kind)))⟩

/-- Match the root, read a present node once, and package its actual fields. -/
def body (kind : CellTy) {signatures : List Signature} :
    Stmt signatures [.option (.node kind)]
      (.option (.prod kind.toTy (.option (.node kind)))) :=
  .matchOption (.var .here)
    (.letPrim (.none (.prod kind.toTy (.option (.node kind)))) (.ret (.var .here)))
    (.readNode (.var .here) (.letPrim (.some (.var .here)) (.ret (.var .here))))

/-- The same source operation as a callable entry, with no external calls. -/
def program (kind : CellTy) : Program [signature kind] where
  body fn := Fin.cases (body kind) (fun index => Fin.elim0 index) fn

/-- The sole actual source function in this table. -/
def entry (kind : CellTy) : Fin [signature kind].length :=
  ⟨0, Nat.zero_lt_one⟩

@[simp] theorem program_body (kind : CellTy) :
    (program kind).body (entry kind) = body kind := rfl

/-- Empty-root decomposition returns `none` without touching any local or heap object. -/
theorem body_exec_none {signatures : List Signature} (program : Program signatures)
    (kind : CellTy) (initial : State [.option (.node kind)])
    (selected : initial.locals.head = none) :
    Exec program (body kind) initial initial (.returned none) := by
  exact .matchNone selected (.letPrim (.ret (.var .here) _))

/-- Nonempty decomposition performs the actual typed lookup and returns its
head and original tail while preserving the entire source state. -/
theorem body_exec_some {signatures : List Signature} (program : Program signatures)
    (kind : CellTy) (initial : State [.option (.node kind)])
    {ref : NodeRef kind} {head : CellValue kind} {tail : Option (NodeRef kind)}
    (selected : initial.locals.head = some ref)
    (found : initial.heap.node? kind ref.object = some (head, tail)) :
    Exec program (body kind) initial initial (.returned (some (kind.toValue head, tail))) := by
  exact .matchSome (finish := State.cons (τ := .node kind) ref initial) selected
    (.readNode (finish := State.cons (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail) (State.cons (τ := .node kind) ref initial)) found
      (.letPrim (.ret (.var .here) _)))

/-- Native cell payloads reuse the existing Nat and Bool observations. -/
def cellRepresentation (kind : CellTy) : Representation (CellValue kind) kind.toTy :=
  Representation.cell kind

/-- Scalar observation is equality with the existing source-cell conversion. -/
@[simp] theorem cellRepresentation_rel (kind : CellTy) (head : CellValue kind)
    (value : Value kind.toTy) (heap : Heap) :
    (cellRepresentation kind).Rel head value heap ↔ kind.toValue head = value := by
  cases kind <;> rfl

/-- A returned head and shared tail are observed in the same actual heap. -/
def resultRepresentation (kind : CellTy) :
    Representation (Option (CellValue kind × List (CellValue kind)))
      (.option (.prod kind.toTy (.option (.node kind)))) :=
  ((cellRepresentation kind).prod (Representation.list kind)).option

/-- Decomposition returns the ordinary empty/cons view of the represented list.
The exact unchanged heap preserves every other list, including shared tails. -/
theorem total (kind : CellTy) (values : List (CellValue kind)) :
    FunctionTotal (program kind) (entry kind)
      (fun args heap => (Representation.list kind).Rel values args.head heap)
      (fun _ initial value finish =>
        (resultRepresentation kind).Rel
          (values.head?.map (fun head => (head, values.tail))) value finish ∧ finish = initial) := by
  intro args heap observed
  change NodeRef.Contents heap args.head values at observed
  generalize selected : args.head = root at observed
  cases observed with
  | nil =>
      refine ⟨⟨args, heap⟩, none, body_exec_none (program kind) kind ⟨args, heap⟩ selected, ?_, rfl⟩
      exact Representation.option_none _ heap
  | @cons ref head tail rest found contents =>
      refine ⟨⟨args, heap⟩, some (kind.toValue head, tail),
        body_exec_some (program kind) kind ⟨args, heap⟩ selected found, ?_, rfl⟩
      change (cellRepresentation kind).Rel head (kind.toValue head) heap ∧
        (Representation.list kind).Rel rest tail heap
      exact ⟨(cellRepresentation_rel kind head (kind.toValue head) heap).mpr rfl, contents⟩

/-- Ordinary List input and optional head/tail output at the actual invocation heaps. -/
def representation (kind : CellTy) :
    FunctionRepresentation (List (CellValue kind))
      (fun _ => Option (CellValue kind × List (CellValue kind))) (signature kind) :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.single (Representation.list kind)) (fun _ => resultRepresentation kind)

/-- The actual source operation refines ordinary Lean List decomposition.
Its stronger exact-state and exact-heap frames are available above. -/
theorem refines (kind : CellTy) :
    RepresentedFunction.Refines (program kind) (entry kind) (representation kind)
      (fun _ => True) (fun values => values.head?.map (fun head => (head, values.tail))) := by
  intro values _
  apply (total kind values).consequence (fun _ _ observed => observed)
  intro args initial value finish _ result
  exact result.1

end Complexity.Language.List.Uncons
