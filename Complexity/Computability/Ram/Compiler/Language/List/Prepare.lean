/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Language.Heap.Prefix

/-!
# Preparing a current linked input in retained RAM memory

A preparation consists of actual compiled `List.Cons` invocations, starting
from the current memory and extending its heap. The supplied current values
are proof-side external input, not a source callback or an already represented
root. Each node is really allocated and its invocation steps are counted.

The original order is retained by preparing the tail before the head. An
existing represented suffix can be shared. Exact old object contents and their
placements survive, including mutable arrays and aliases. The final world can
be used by a later preloaded invocation without bootstrapping its memory.

The cost bounds the allocating invocations, not external list traversal,
transport, scalar loading, or a continuous driver. In particular, keeping an
old rooted value's word encoding does not save its registers across the helper
calls. Those physical driver operations remain a separate boundary.
-/

namespace Ram.LanguageCompiler.List.Prepare

open Complexity.Language

variable (kind : CellTy) {w heapLimit : Nat}

/-- A sequence of real allocating invocations for the current input prefix.
Each continuation uses the preceding outcome's complete memory and placement.
The empty prefix allocates nothing and preserves the supplied tail. -/
inductive Run : _root_.List (CellValue kind) → Option (NodeRef kind) →
    Session.State w heapLimit → Option (NodeRef kind) →
    Session.State w heapLimit → Nat → Prop
  | nil (tail current) : Run [] tail current tail current 0
  | cons {head values tail current root middle steps}
      (rest : Run values tail current root middle steps)
      (outcome : FunctionArenaExecution (List.Cons.program kind) (List.Cons.entry kind)
        0 heapLimit middle.placement (List.Cons.args kind head root)
        middle.heap middle.entry) :
      Run (head :: values) tail current outcome.value (Session.State.ofExecution outcome)
        (steps + outcome.result.steps)

variable {kind}

/-- The prepared root observes the original mathematical list, while every old
object and placement is retained. This also frames overlapping old arrays. -/
theorem Run.observed {values suffix : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} (run : Run kind values tail current root finish steps)
    (observed : (Representation.list kind).Rel suffix tail current.heap) :
    (Representation.list kind).Rel (values ++ suffix) root finish.heap ∧
      _root_.List.IsPrefix current.heap.objects.toList finish.heap.objects.toList ∧
      current.heap.ShapeExtends finish.heap ∧
      Placement.Agrees current.heap current.placement finish.placement := by
  induction run with
  | nil => exact ⟨observed, List.prefix_refl _, Heap.ShapeExtends.refl _,
      Placement.Agrees.refl _ _⟩
  | @cons head values tail current root middle steps rest outcome ih =>
      obtain ⟨represented, extension, shape, agreement⟩ := ih observed
      have property := outcome.post (List.Cons.total kind head (values ++ suffix))
        ⟨(Representation.cell_rel kind head (kind.toValue head) middle.heap).mpr rfl,
          represented⟩
      refine ⟨property.1, ?_, shape.trans property.2.2.2, ?_⟩
      · change _root_.List.IsPrefix current.heap.objects.toList outcome.heap.objects.toList
        rw [property.2.1]
        exact extension.trans (middle.heap.objects_prefix_cons head root)
      · exact agreement.trans_of_shape outcome.agreement shape

/-- Existing state words survive preparation without reconstruction from a
mathematical model. This is placement stability, not a register-save program. -/
theorem Run.retained_words {values suffix : _root_.List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {current finish : Session.State w heapLimit}
    {steps : Nat} (run : Run kind values tail current root finish steps)
    (observed : (Representation.list kind).Rel suffix tail current.heap)
    {τ : Ty} (value : Value τ) (rooted : ValueRooted current.heap value) :
    ValueRooted finish.heap value ∧
      valueWords current.placement value = valueWords finish.placement value := by
  obtain ⟨_, _, shape, agreement⟩ := run.observed observed
  exact ⟨rooted.mono shape, agreement.valueWords rooted⟩

/-- Every current finite input has a genuine preparation when its scalar words
fit and the actual arena has three words per new node. The bound is derived
from the compiled constructor's existing invocation theorem. -/
theorem exists_le (kind : CellTy) (values suffix : _root_.List (CellValue kind))
    (tail : Option (NodeRef kind)) (current : Session.State w heapLimit)
    (capacity : FunctionCapacity (List.Cons.program kind) (List.Cons.entry kind)
      w 0 heapLimit)
    (fits : ∀ value ∈ values, ValueFits w (kind.toValue value))
    (space : current.cursor + 3 * values.length ≤ heapLimit)
    (observed : (Representation.list kind).Rel suffix tail current.heap) :
    ∃ (root : Option (NodeRef kind)) (finish : Session.State w heapLimit) (steps : Nat),
      Run kind values tail current root finish steps ∧
      (Representation.list kind).Rel (values ++ suffix) root finish.heap ∧
      finish.cursor = current.cursor + 3 * values.length ∧
      steps ≤ values.length * List.Cons.steps kind := by
  induction values generalizing tail current with
  | nil =>
      exact ⟨tail, current, 0, .nil tail current, observed, by simp, by simp⟩
  | cons head values ih =>
      have tailSpace : current.cursor + 3 * values.length ≤ heapLimit := by
        simp only [List.length_cons] at space
        omega
      obtain ⟨root, middle, steps, rest, represented, cursor, bound⟩ :=
        ih tail current (fun value member => fits value (List.mem_cons_of_mem _ member))
          tailSpace observed
      have remaining : middle.cursor + 3 ≤ heapLimit := by
        rw [cursor]
        simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using space
      obtain ⟨outcome, result, _, _, _, finalCursor, cost⟩ :=
        List.Cons.execute_le kind head (values ++ suffix) root middle.heap
          middle.entry middle.placement capacity middle.arena
          (fits head List.mem_cons_self) remaining represented
      refine ⟨outcome.value, Session.State.ofExecution outcome,
        steps + outcome.result.steps, .cons rest outcome, result, ?_, ?_⟩
      · change outcome.cursor = current.cursor + 3 * (head :: values).length
        rw [finalCursor, cursor]
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      · simpa only [List.length_cons, Nat.add_mul, Nat.one_mul] using
          Nat.add_le_add bound cost

end Ram.LanguageCompiler.List.Prepare
