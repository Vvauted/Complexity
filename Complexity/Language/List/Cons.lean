/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.List
import Complexity.Language.RepresentedFunction

/-!
# Constructing represented linked lists

`List.Cons.body` allocates one actual node with `Stmt.consNode` and returns its
fresh reference as an optional list root. Its tail is the supplied reference:
the operation neither traverses nor copies the existing chain, and allocation
itself does not perform a runtime tail-validity check.

The mathematical contract reuses the existing cell and linked-list observations
to identify the result with ordinary `List.cons`. It also records the exact
allocated heap, the exact fresh returned root and preservation of old heap
shapes. Every old represented list consequently remains valid, including lists
sharing the tail. These are source correctness facts, without machine capacity
or instruction-cost premises.
-/

namespace Complexity.Language.List.Cons

/-- A scalar head and an optional linked tail produce an optional linked root. -/
def signature (kind : CellTy) : Signature :=
  ⟨[kind.toTy, .option (.node kind)], .option (.node kind)⟩

/-- The constructor's ordinary operands in its source signature's order. -/
def args (kind : CellTy) (head : CellValue kind) (tail : Option (NodeRef kind)) :
    Env (signature kind).params :=
  Env.cons (τ := kind.toTy) (kind.toValue head)
    (Env.cons (τ := .option (.node kind)) tail Env.empty)

/-- Allocate the actual head/tail node and return its fresh root. -/
def body (kind : CellTy) {signatures : List Signature} :
    Stmt signatures [kind.toTy, .option (.node kind)] (.option (.node kind)) :=
  .consNode (.var .here) (.var (.there .here))
    (.letPrim (.some (.var .here)) (.ret (.var .here)))

/-- The same source operation as a callable entry, without external calls. -/
def program (kind : CellTy) : Program [signature kind] where
  body fn := Fin.cases (body kind) (fun index => Fin.elim0 index) fn

/-- The sole actual source function in this table. -/
def entry (kind : CellTy) : Fin [signature kind].length :=
  ⟨0, Nat.zero_lt_one⟩

@[simp] theorem program_body (kind : CellTy) :
    (program kind).body (entry kind) = body kind := rfl

/-- Construction preserves the original locals and returns the actual freshly
allocated root. This execution rule accepts the supplied tail without a lookup. -/
theorem body_exec {signatures : List Signature} (program : Program signatures)
    (kind : CellTy) (initial : State [kind.toTy, .option (.node kind)]) :
    let allocated := initial.heap.cons (kind.ofValue initial.locals.head)
      initial.locals.tail.head
    Exec program (body kind) initial ⟨initial.locals, allocated.2⟩
      (.returned (some allocated.1)) := by
  let allocated := initial.heap.cons (kind.ofValue initial.locals.head)
    initial.locals.tail.head
  exact .consNode (finish := State.cons (τ := .node kind) allocated.1
    ⟨initial.locals, allocated.2⟩) (.letPrim (.ret (.var .here) _))

/-- A represented head and tail produce their ordinary mathematical cons.
The exact fresh root and allocated heap are retained alongside old heap shapes;
existing list observations transport through `Representation.list_mono`. -/
theorem total (kind : CellTy) (head : CellValue kind) (values : List (CellValue kind)) :
    FunctionTotal (program kind) (entry kind)
      (fun args heap => (Representation.cell kind).Rel head args.head heap ∧
        (Representation.list kind).Rel values args.tail.head heap)
      (fun args initial value finish =>
        (Representation.list kind).Rel (head :: values) value finish ∧
        finish = (initial.cons head args.tail.head).2 ∧
        value = some (initial.cons head args.tail.head).1 ∧
        initial.ShapeExtends finish) := by
  intro args heap ⟨scalar, observed⟩
  have head_eq : kind.ofValue args.head = head := by
    rw [← (Representation.cell_rel kind head args.head heap).mp scalar,
      CellTy.ofValue_toValue]
  have executed := body_exec (program kind) kind ⟨args, heap⟩
  change Exec (program kind) (body kind) ⟨args, heap⟩
    ⟨args, (heap.cons (kind.ofValue args.head) args.tail.head).2⟩
    (.returned (some (heap.cons (kind.ofValue args.head) args.tail.head).1)) at executed
  rw [head_eq] at executed
  exact ⟨_, _, executed, Heap.cons_contents head observed, rfl, rfl,
    heap.shapeExtends_cons head args.tail.head⟩

/-- The ordinary head/list input and linked-list output use their existing
representations at the actual invocation heaps. -/
def representation (kind : CellTy) :
    FunctionRepresentation (CellValue kind × List (CellValue kind))
      (fun _ => List (CellValue kind)) (signature kind) :=
  FunctionRepresentation.ofResult
    (ArgumentRepresentation.cons (Representation.cell kind)
      (ArgumentRepresentation.single (Representation.list kind)))
    (fun _ => Representation.list kind)

/-- The actual allocating source operation refines ordinary Lean `List.cons`.
Its exact-heap, fresh-root and preservation guarantees remain available in `total`. -/
theorem refines (kind : CellTy) :
    RepresentedFunction.Refines (program kind) (entry kind) (representation kind)
      (fun _ => True) (fun input => input.1 :: input.2) := by
  intro input _
  apply (total kind input.1 input.2).consequence (fun _ _ observed => observed)
  intro args initial value finish _ result
  exact result.1

end Complexity.Language.List.Cons
