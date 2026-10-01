/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Cons
import Complexity.Language.Eval.Verification
import Complexity.Language.Heap.Prefix

/-!
# Source meaning of current linked-input preparation

The relation records invocations of the existing source constructor, in
tail-before-head order. It neither evaluates a host callback nor supplies a
pre-existing root for an external list. Source preparation is total without a
word width, storage budget or cost premise. RAM realization is separate.
-/

namespace Complexity.Language.List.Prepare

variable (kind : CellTy)

/-- Actual source constructor calls that prepend the current external values
to a retained tail. No future input or private-state reconstruction occurs. -/
inductive Run : List (CellValue kind) → Option (NodeRef kind) → Heap →
    Option (NodeRef kind) → Heap → Prop
  | nil (tail heap) : Run [] tail heap tail heap
  | cons {head values tail heap root middle result finish}
      (rest : Run values tail heap root middle)
      (called : (Cons.program kind).eval (Cons.entry kind) (Cons.args kind head root)
        middle = Part.some (.ok result, finish)) :
      Run (head :: values) tail heap result finish

variable {kind}

/-- Preparation always has a finite source execution, independently of any
finite machine's capacity. The supplied tail need not be inspected or copied. -/
theorem exists_run (kind : CellTy) (values : List (CellValue kind))
    (tail : Option (NodeRef kind)) (heap : Heap) :
    ∃ root finish, Run kind values tail heap root finish := by
  induction values with
  | nil => exact ⟨tail, heap, .nil tail heap⟩
  | cons head values ih =>
      obtain ⟨root, middle, rest⟩ := ih
      refine ⟨some (middle.cons head root).1, (middle.cons head root).2,
        .cons rest ?_⟩
      apply Program.eval_eq_ok_iff.mpr
      refine ⟨⟨Cons.args kind head root, (middle.cons head root).2⟩, ?_, rfl⟩
      simpa only [Cons.args, Env.head_cons, Env.tail_cons, CellTy.ofValue_toValue] using
        Cons.body_exec (Cons.program kind) kind ⟨Cons.args kind head root, middle⟩

/-- Ordinary list contents and every old object survive these real calls. -/
theorem Run.observed {values suffix : List (CellValue kind)}
    {tail root : Option (NodeRef kind)} {heap finish : Heap}
    (run : Run kind values tail heap root finish)
    (observed : (Representation.list kind).Rel suffix tail heap) :
    (Representation.list kind).Rel (values ++ suffix) root finish ∧
      List.IsPrefix heap.objects.toList finish.objects.toList ∧
      heap.ShapeExtends finish := by
  induction run with
  | nil => exact ⟨observed, List.prefix_refl _, Heap.ShapeExtends.refl _⟩
  | @cons head values tail heap root middle result finish rest called ih =>
      obtain ⟨represented, extension, shape⟩ := ih observed
      obtain ⟨finalState, execution, sameHeap⟩ := Program.eval_eq_ok_iff.mp called
      have property := (Cons.total kind head (values ++ suffix)).postcondition
        (args := Cons.args kind head root) (heap := middle)
        ⟨(Representation.cell_rel kind head (kind.toValue head) middle).mpr rfl,
          represented⟩ execution
      rw [sameHeap] at property
      refine ⟨property.1, ?_, shape.trans property.2.2.2⟩
      rw [property.2.1]
      exact extension.trans (middle.objects_prefix_cons head root)

/-- Fixed current values and the actual initial heap determine the complete
preparation result. This does not assert uniqueness of arbitrary list layouts. -/
theorem Run.deterministic {values : List (CellValue kind)} {tail : Option (NodeRef kind)}
    {heap finish₁ finish₂ : Heap} {root₁ root₂ : Option (NodeRef kind)}
    (first : Run kind values tail heap root₁ finish₁)
    (second : Run kind values tail heap root₂ finish₂) :
    root₁ = root₂ ∧ finish₁ = finish₂ := by
  induction first generalizing root₂ finish₂ with
  | nil =>
      cases second
      exact ⟨rfl, rfl⟩
  | cons rest called ih =>
      cases second with
      | cons rest' called' =>
          obtain ⟨rfl, rfl⟩ := ih rest'
          have same := Part.some_injective (called.symm.trans called')
          exact ⟨Except.ok.inj (congrArg Prod.fst same), congrArg Prod.snd same⟩

end Complexity.Language.List.Prepare
