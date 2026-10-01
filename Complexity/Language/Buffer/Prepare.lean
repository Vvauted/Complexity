/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Replicate
import Complexity.Language.Heap.Prefix

/-!
# Preparing a current natural array in a retained heap

Preparation invokes the existing initialized allocator, then writes each current
external scalar into the fresh buffer. It does not accept a preloaded buffer or
reconstruct private state. The actual writes determine the final contents and
preserve every old object, including overlapping old views and immutable nodes.

The relations compose existing source operations, without a host callback or
new evaluator. Finite-word readiness and the cost of the same compiled calls
are separate. External traversal and port transport are not represented here.
-/

namespace Complexity.Language.Buffer.Prepare

/-- The scalar write used by current-array preparation. -/
def writeSignature : Signature := ⟨[.buffer .nat, .nat, .nat], .unit⟩

/-- Arguments of the fixed scalar-write entry. -/
def writeArgs (buffer : Buffer .nat) (index value : Nat) : Env writeSignature.params :=
  Env.cons buffer (Env.cons index (Env.cons value Env.empty))

/-- A real source write followed by an ordinary unit return. -/
def writeBody {signatures : List Signature} : Stmt signatures writeSignature.params .unit :=
  .seq (.write (.var .here) (.var (.there .here)) (.var (.there (.there .here))))
    (.ret .unit)

/-- A closed source program containing only the scalar-write entry. -/
def writeProgram : Program [writeSignature] where
  body fn := Fin.cases writeBody (fun index => Fin.elim0 index) fn

/-- Select the scalar-write body in its closed program. -/
def writeEntry : Fin [writeSignature].length := ⟨0, Nat.zero_lt_one⟩

/-- A successful primitive write is the execution of this same callable body. -/
theorem write_exec {buffer : Buffer .nat} {index value : Nat} {heap finish : Heap}
    (written : heap.write buffer index value = .ok finish) :
    Exec writeProgram (writeProgram.body writeEntry) ⟨writeArgs buffer index value, heap⟩
      ⟨writeArgs buffer index value, finish⟩ (.returned ()) :=
  .seqNormal (.write written) (.ret .unit _)

/-- The selected source entry succeeds exactly when the actual heap write does. -/
theorem write_eval_iff {buffer : Buffer .nat} {index value : Nat} {heap finish : Heap} :
    writeProgram.eval writeEntry (writeArgs buffer index value) heap =
        Part.some (.ok (), finish) ↔
      heap.write buffer index value = .ok finish := by
  constructor
  · intro called
    obtain ⟨finalState, execution, sameHeap⟩ := Program.eval_eq_ok_iff.mp called
    change Exec writeProgram (writeBody) ⟨writeArgs buffer index value, heap⟩
      finalState (.returned ()) at execution
    cases execution with
    | seqNormal first second =>
        cases first with
        | write written =>
            cases second
            simpa only [← sameHeap] using written
    | seqReturn first => cases first
  · intro written
    exact Program.eval_eq_ok_iff.mpr ⟨_, write_exec written, rfl⟩

/-- The first count cells are filled by actual writes in their original order.
Each value comes only from the current external array. -/
inductive Fill (values : Array Nat) (buffer : Buffer .nat) :
    Nat → Heap → Heap → Prop
  | zero (heap) : Fill values buffer 0 heap heap
  | succ {count heap middle finish}
      (rest : Fill values buffer count heap middle)
      (bound : count < values.size)
      (written : middle.write buffer count values[count] = .ok finish) :
      Fill values buffer (count + 1) heap finish

/-- Existing shapes survive every actual cell write. -/
theorem Fill.shape {values : Array Nat} {buffer : Buffer .nat}
    {count : Nat} {heap finish : Heap} (run : Fill values buffer count heap finish) :
    heap.ShapeExtends finish := by
  induction run with
  | zero => exact Heap.ShapeExtends.refl _
  | succ rest bound written ih => exact ih.trans (Heap.shapeExtends_write written)

/-- Every filled cell contains the corresponding external value. -/
theorem Fill.read {values : Array Nat} {buffer : Buffer .nat}
    {count : Nat} {heap finish : Heap} (run : Fill values buffer count heap finish)
    {index : Nat} (before : index < count) (bound : index < values.size) :
    finish.read buffer index = .ok values[index] := by
  induction run with
  | zero => omega
  | @succ count heap middle finish rest currentBound written ih =>
      by_cases same : count = index
      · subst index
        exact Heap.read_write written
      · rw [Heap.read_write_of_ne_cell written rfl (by omega)]
        exact ih (by omega)

/-- Writes into a newly allocated object retain the exact old object prefix. -/
theorem Fill.prefix {values : Array Nat} {buffer : Buffer .nat}
    {count : Nat} {old heap finish : Heap} (run : Fill values buffer count heap finish)
    (extension : List.IsPrefix old.objects.toList heap.objects.toList)
    (fresh : old.objects.size ≤ buffer.object) :
    List.IsPrefix old.objects.toList finish.objects.toList := by
  induction run with
  | zero => exact extension
  | succ rest bound written ih => exact Heap.objects_prefix_write (ih extension) fresh written

/-- Every finite prefix can be written into a valid array of the same extent.
No proposed budget or machine capacity is required for source totality. -/
theorem Fill.exists_run (values : Array Nat) (buffer : Buffer .nat)
    (count : Nat) (before : count ≤ values.size) (heap : Heap)
    (valid : buffer.Valid heap) (size : buffer.length = values.size) :
    ∃ finish, Fill values buffer count heap finish := by
  induction count with
  | zero => exact ⟨heap, .zero heap⟩
  | succ count ih =>
      obtain ⟨middle, rest⟩ := ih (by omega)
      obtain ⟨contents, observed⟩ := (valid.mono rest.shape).contents
      have currentBound : count < values.size := by omega
      obtain ⟨finish, written, _⟩ := observed.write_exists
        (index := count) (by rw [observed.size_eq, size]; exact currentBound)
        values[count]
      exact ⟨finish, .succ rest currentBound written⟩

/-- Allocate a fresh real buffer before filling it. Even an empty input has its
own fresh object. The source allocator is the existing Replicate entry. -/
def Run (values : Array Nat) (heap : Heap) (buffer : Buffer .nat) (finish : Heap) : Prop :=
  ∃ allocated,
    Replicate.program.eval Replicate.replicateNatId
      (Replicate.replicateNat_args values.size 0) heap = Part.some (.ok buffer, allocated) ∧
    Fill values buffer values.size allocated finish

private theorem allocated_eq {values : Array Nat} {heap allocated : Heap}
    {buffer : Buffer .nat}
    (called : Replicate.program.eval Replicate.replicateNatId
      (Replicate.replicateNat_args values.size 0) heap = Part.some (.ok buffer, allocated)) :
    buffer = (heap.alloc (τ := .nat) values.size 0).1 ∧
      allocated = (heap.alloc (τ := .nat) values.size 0).2 := by
  rw [Replicate.replicateNat_observe, Replicate.replicateNat_eval] at called
  have same := Part.some_injective called
  exact ⟨(Except.ok.inj (congrArg Prod.fst same)).symm, (congrArg Prod.snd same).symm⟩

/-- Every current array has an actual source preparation. -/
theorem exists_run (values : Array Nat) (heap : Heap) :
    ∃ buffer finish, Run values heap buffer finish := by
  obtain ⟨finish, filled⟩ := Fill.exists_run values
    (heap.alloc (τ := .nat) values.size 0).1 values.size (Nat.le_refl _)
    (heap.alloc (τ := .nat) values.size 0).2 (heap.alloc_valid _ _) rfl
  refine ⟨_, finish, _, ?_, filled⟩
  rw [Replicate.replicateNat_observe]
  exact Replicate.replicateNat_eval _ _ _

/-- The preparation gives the original mathematical array, fresh descriptor,
exact old-object preservation, and the same final heap shape. -/
theorem Run.observed {values : Array Nat} {heap finish : Heap} {buffer : Buffer .nat}
    (run : Run values heap buffer finish) :
    buffer.Contents finish values ∧
      buffer.object = heap.objects.size ∧ buffer.offset = 0 ∧ buffer.length = values.size ∧
      List.IsPrefix heap.objects.toList finish.objects.toList ∧ heap.ShapeExtends finish := by
  obtain ⟨allocated, called, filled⟩ := run
  obtain ⟨rfl, rfl⟩ := allocated_eq called
  refine ⟨Contents.of_read ((heap.alloc_valid _ _).mono filled.shape) rfl
    (fun _ bound => filled.read bound bound), rfl, rfl, rfl,
    filled.prefix (heap.objects_prefix_alloc _ _) (Nat.le_refl _),
    (heap.shapeExtends_alloc _ _).trans filled.shape⟩

end Complexity.Language.Buffer.Prepare
