/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Basic
import Complexity.Language.Heap.Node

/-!
# Native actions for immutable nodes

These exception/state actions expose the existing node allocation and typed
lookup at the actual current heap. Allocation appends one node without checking
or traversing its tail; valid-chain premises belong to its mathematical contract.
Reading returns that node's stored head and identical tail handle, or a finite
heap fault for an absent or wrongly tagged object. Neither read outcome changes
the heap. The wrappers add no evaluator, source syntax or machine cost model.
-/

namespace Complexity.Language.NodeRef

/-- Append the actual immutable node, sharing the supplied tail without traversal
or validation. Source allocation does not impose finite-machine capacity. -/
def consM {kind : CellTy} (head : CellValue kind) (tail : Option (NodeRef kind)) :
    ExceptT Fault (StateT Heap Part) (NodeRef kind) := fun heap =>
  let allocated := heap.cons head tail
  Part.some (.ok allocated.1, allocated.2)

/-- Allocation returns precisely the fresh reference and heap from `Heap.cons`. -/
theorem consM_eq_ok {kind : CellTy} (head : CellValue kind)
    (tail : Option (NodeRef kind)) (heap : Heap) :
    consM head tail heap =
      Part.some (.ok (heap.cons head tail).1, (heap.cons head tail).2) := rfl

/-- Read the actual typed node, retaining the current heap on success or failure.
An invalid nonempty reference is a heap fault, not an empty list. -/
def readM {kind : CellTy} (ref : NodeRef kind) :
    ExceptT Fault (StateT Heap Part) (CellValue kind × Option (NodeRef kind)) := fun heap =>
  Part.some (match heap.node? kind ref.object with
    | some contents => (.ok contents, heap)
    | none => (.error (.heap .invalidObject), heap))

/-- Successful typed lookup supplies the same head and tail to the action. -/
theorem readM_eq_ok {kind : CellTy} {heap : Heap} {ref : NodeRef kind}
    {head : CellValue kind} {tail : Option (NodeRef kind)}
    (found : heap.node? kind ref.object = some (head, tail)) :
    ref.readM heap = Part.some (.ok (head, tail), heap) := by
  simp only [readM, found]

/-- Missing or wrongly tagged nodes produce a finite fault without changing the heap. -/
theorem readM_eq_error {kind : CellTy} {heap : Heap} {ref : NodeRef kind}
    (missing : heap.node? kind ref.object = none) :
    ref.readM heap = Part.some (.error (.heap .invalidObject), heap) := by
  simp only [readM, missing]

end Complexity.Language.NodeRef
