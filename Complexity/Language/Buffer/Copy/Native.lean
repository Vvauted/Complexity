/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Language.Representation
import Complexity.Language.Verification.Heap

/-!
# Native observations of allocating array copy and append

`copyEval` and `appendEval` invoke the existing source entries with their actual
buffer arguments. The ordinary array result, heap-shape frame and preservation
of every old array observation follow from those same source contracts.

The contents frame is stronger than heap-shape preservation: copying writes the
fresh result while retaining old mutable contents, including overlapping input
views. It does not make arbitrary source writes preserve arrays or grant returned
storage permanent immutability. Input loading and resource bounds remain separate.
-/

namespace Complexity.Language.Buffer.Copy

/-- Invoke the existing allocating copy entry with its actual source buffer. -/
noncomputable def copyEval (source : Buffer .nat) :
    ExceptT Fault (StateT Heap Part) (Buffer .nat) :=
  program.eval copyId (Env.cons source Env.empty)

/-- Invoke the existing allocating append entry with both actual source buffers. -/
noncomputable def appendEval (left right : Buffer .nat) :
    ExceptT Fault (StateT Heap Part) (Buffer .nat) :=
  program.eval appendId (Env.cons left (Env.cons right Env.empty))

/-- The actual copy returns the mathematical input in its final heap, retaining
both immutable node observations and every previously observed mutable array. -/
theorem copy_eval_exists_preserving (values : Array Nat) (source : Buffer .nat) (heap : Heap)
    (observed : (Representation.array .nat).Rel values source heap) :
    ∃ returned finish,
      Copy.copy source heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel values returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  obtain ⟨returned, finish, evaluated, ⟨contents, _, preserved⟩, shape⟩ :=
    (Buffer.copy_total values).with_heap_shapeExtends.eval_spec
      (args := Env.cons source Env.empty) (initialHeap := heap) observed
  exact ⟨returned, finish, evaluated, contents, shape, preserved⟩

/-- The actual append returns ordinary array append in fresh storage while all
old views retain their contents. The two inputs need not be disjoint. -/
theorem append_eval_exists_preserving (leftValues rightValues : Array Nat)
    (left right : Buffer .nat) (heap : Heap)
    (leftObserved : (Representation.array .nat).Rel leftValues left heap)
    (rightObserved : (Representation.array .nat).Rel rightValues right heap) :
    ∃ returned finish,
      Copy.append left right heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (leftValues ++ rightValues) returned finish ∧
      heap.ShapeExtends finish ∧ Buffer.PreservesContents heap finish := by
  obtain ⟨returned, finish, evaluated, ⟨contents, _, preserved⟩, shape⟩ :=
    (Buffer.append_total leftValues rightValues).with_heap_shapeExtends.eval_spec
      (args := Env.cons left (Env.cons right Env.empty)) (initialHeap := heap)
      ⟨leftObserved, rightObserved⟩
  exact ⟨returned, finish, evaluated, contents, shape, preserved⟩

/-- The ordinary relational call interface follows from the same copy execution. -/
theorem copy_eval_exists (values : Array Nat) (source : Buffer .nat) (heap : Heap)
    (observed : (Representation.array .nat).Rel values source heap) :
    ∃ returned finish,
      Copy.copy source heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel values returned finish ∧ heap.ShapeExtends finish := by
  obtain ⟨returned, finish, evaluated, contents, shape, _⟩ :=
    copy_eval_exists_preserving values source heap observed
  exact ⟨returned, finish, evaluated, contents, shape⟩

/-- The ordinary relational call interface follows from the same append execution. -/
theorem append_eval_exists (leftValues rightValues : Array Nat)
    (left right : Buffer .nat) (heap : Heap)
    (leftObserved : (Representation.array .nat).Rel leftValues left heap)
    (rightObserved : (Representation.array .nat).Rel rightValues right heap) :
    ∃ returned finish,
      Copy.append left right heap = Part.some (.ok returned, finish) ∧
      (Representation.array .nat).Rel (leftValues ++ rightValues) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, evaluated, contents, shape, _⟩ :=
    append_eval_exists_preserving leftValues rightValues left right heap leftObserved rightObserved
  exact ⟨returned, finish, evaluated, contents, shape⟩

end Complexity.Language.Buffer.Copy
