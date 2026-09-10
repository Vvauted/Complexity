/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Splay.Program
import Complexity.Language.Eval.Verification

/-!
# Actual field updates of the splay rotations

These contracts describe the two real heap writes performed by a rotation.
Ordinary array contents establish successful reads and writes; the resulting
`Array.set` equations expose the precise field changes to a mathematical tree
representation. The write witnesses also retain frames for unrelated objects,
disjoint views of the same object and untouched cells of either child array.

The left/right buffers need disjoint storage, not distinct object identifiers.
No assumption about a particular heap encoding, word width or time budget is
needed for these source-correctness statements.
-/

namespace Complexity.Language.Examples.Splay

/-- The declared right rotation performs the supplied current-heap accesses.
The witnesses describe real writes in order, not a replacement array evaluator. -/
theorem rotateRight_eval_of_accesses (left right : Buffer .nat)
    (root child middle : Nat) {initial between finish : Heap}
    (readChild : initial.read left root = .ok child)
    (readMiddle : initial.read right child = .ok middle)
    (writeLeft : initial.write left root middle = .ok between)
    (writeRight : between.write right child root = .ok finish) :
    Implementation.rotateRight left right root initial = Part.some (.ok child, finish) := by
  rw [Implementation.rotateRight_eq]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, Pure.pure, StateT.bind, StateT.pure,
    Buffer.readM, Buffer.writeM, readChild, readMiddle, writeLeft, writeRight,
    Part.bind_some]

/-- Swapping the two field arrays exchanges the source behaviors of the two
rotations. This equation is not used to assign either implementation's cost. -/
theorem rotateLeft_eq_rotateRight (left right : Buffer .nat) (root : Nat) :
    Implementation.rotateLeft left right root =
      Implementation.rotateRight right left root := by
  rw [Implementation.rotateLeft_eq, Implementation.rotateRight_eq]

/-- The symmetric rotation retains the actual intermediate shared heap. -/
theorem rotateLeft_eval_of_accesses (left right : Buffer .nat)
    (root child middle : Nat) {initial between finish : Heap}
    (readChild : initial.read right root = .ok child)
    (readMiddle : initial.read left child = .ok middle)
    (writeRight : initial.write right root middle = .ok between)
    (writeLeft : between.write left child root = .ok finish) :
    Implementation.rotateLeft left right root initial = Part.some (.ok child, finish) := by
  rw [rotateLeft_eq_rotateRight]
  exact rotateRight_eval_of_accesses right left root child middle
    readChild readMiddle writeRight writeLeft

/-- Valid ordinary array contents suffice for a right rotation. Its complete
postcondition retains both precise array updates and the two heap-write facts,
so later tree, alias and frame proofs do not have to reopen the implementation. -/
theorem rotateRight_eval (left right : Buffer .nat) (root child : Nat)
    {initial : Heap} {leftValues rightValues : Array Nat}
    (observedLeft : left.Contents initial leftValues)
    (observedRight : right.Contents initial rightValues)
    (separated : left.Disjoint right)
    (rootBound : root < leftValues.size) (childBound : child < rightValues.size)
    (childValue : leftValues[root] = child) :
    ∃ between finish,
      Implementation.rotateRight left right root initial = Part.some (.ok child, finish) ∧
      initial.write left root rightValues[child] = .ok between ∧
      between.write right child root = .ok finish ∧
      left.Contents finish (leftValues.set root rightValues[child] rootBound) ∧
      right.Contents finish (rightValues.set child root childBound) := by
  obtain ⟨between, writeLeft, updatedLeft⟩ :=
    observedLeft.write_exists rootBound rightValues[child]
  have retainedRight := observedRight.write_of_disjoint writeLeft separated
  obtain ⟨finish, writeRight, updatedRight⟩ :=
    retainedRight.write_exists childBound root
  have retainedLeft := updatedLeft.write_of_disjoint writeRight separated.symm
  refine ⟨between, finish, ?_, writeLeft, writeRight, retainedLeft, updatedRight⟩
  apply rotateRight_eval_of_accesses left right root child rightValues[child]
  · simpa only [childValue] using observedLeft.read rootBound
  · exact observedRight.read childBound
  · exact writeLeft
  · exact writeRight

/-- Valid ordinary array contents give the symmetric left-rotation contract,
including both real writes and the current contents of both field arrays. -/
theorem rotateLeft_eval (left right : Buffer .nat) (root child : Nat)
    {initial : Heap} {leftValues rightValues : Array Nat}
    (observedLeft : left.Contents initial leftValues)
    (observedRight : right.Contents initial rightValues)
    (separated : left.Disjoint right)
    (rootBound : root < rightValues.size) (childBound : child < leftValues.size)
    (childValue : rightValues[root] = child) :
    ∃ between finish,
      Implementation.rotateLeft left right root initial = Part.some (.ok child, finish) ∧
      initial.write right root leftValues[child] = .ok between ∧
      between.write left child root = .ok finish ∧
      left.Contents finish (leftValues.set child root childBound) ∧
      right.Contents finish (rightValues.set root leftValues[child] rootBound) := by
  obtain ⟨between, finish, executed, writeRight, writeLeft, updatedRight, updatedLeft⟩ :=
    rotateRight_eval right left root child observedRight observedLeft
      separated.symm rootBound childBound childValue
  exact ⟨between, finish, by simpa only [rotateLeft_eq_rotateRight] using executed,
    writeRight, writeLeft, updatedLeft, updatedRight⟩

/-- Two rotation writes preserve every unrelated borrowed view, including a
keys array or disjoint slices of either underlying object. The two write facts
are obtained directly from either rotation's operational contract. -/
theorem contents_of_rotation_writes {first second : Buffer .nat}
    {firstIndex firstValue secondIndex secondValue : Nat} {initial between finish : Heap}
    (writeFirst : initial.write first firstIndex firstValue = .ok between)
    (writeSecond : between.write second secondIndex secondValue = .ok finish)
    {kind : CellTy} {other : Buffer kind} {contents : Array (CellValue kind)}
    (observed : other.Contents initial contents)
    (outsideFirst : first.Disjoint other) (outsideSecond : second.Disjoint other) :
    other.Contents finish contents :=
  (observed.write_of_disjoint writeFirst outsideFirst).write_of_disjoint
    writeSecond outsideSecond

end Complexity.Language.Examples.Splay
