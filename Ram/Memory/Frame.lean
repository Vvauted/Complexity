/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Memory.Indexed
import Ram.Verification.Total
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Function

/-!
# Framing ordinary heap models across a whole block

An endpoint frame is the standard assertion `Set.EqOn after before writesᶜ`.
It preserves every indexed model whose address range is disjoint from the
possible changed cells, as well as any heap predicate with explicitly localized
dependence. No new memory, effect, ownership or allocation datatype is needed.

These rules retain the existing safe execution. They do not infer a frame from
the program's syntax, assert that intermediate states preserve the same cells,
or identify the set `writes` with an execution trace of write events. A block
may temporarily change and restore a cell while satisfying an endpoint frame.
-/

namespace Ram

namespace IndexedRep

variable {ι : Type*} {before after : Word w → Word w}
  {address : ι → Word w} {values : ι → Word w} {writes : Set (Word w)}

/-- The standard range of an address function is exactly the set of cells
needed to preserve its represented mathematical values. -/
theorem congr_eqOn (h : IndexedRep before address values)
    (hmem : Set.EqOn after before (Set.range address)) :
    IndexedRep after address values :=
  h.congr_mem (fun i => hmem ⟨i, rfl⟩)

/-- A whole-block endpoint frame preserves any disjoint indexed view. -/
theorem frame (h : IndexedRep before address values)
    (hframe : Set.EqOn after before writesᶜ)
    (hdisjoint : Disjoint (Set.range address) writes) :
    IndexedRep after address values :=
  h.congr_eqOn (Set.EqOn.mono
    (fun _ hi => hdisjoint.notMem_of_mem_left hi) hframe)

end IndexedRep

namespace Source.IndexedAt

variable {ι : Type*} {heapLimit : Nat} {s t : State w}
  {address : ι → Word w} {values : ι → Word w} {writes : Set (Word w)}

theorem congr_eqOn (h : IndexedAt heapLimit address values s)
    (hmem : Set.EqOn t.mem s.mem (Set.range address)) :
    IndexedAt heapLimit address values t := ⟨h.1.congr_eqOn hmem, h.2⟩

/-- Heap membership remains part of the assertion; framing changes neither
the address layout nor its explicit source-heap bound. -/
theorem frame (h : IndexedAt heapLimit address values s)
    (hframe : Set.EqOn t.mem s.mem writesᶜ)
    (hdisjoint : Disjoint (Set.range address) writes) :
    IndexedAt heapLimit address values t := ⟨h.1.frame hframe hdisjoint, h.2⟩

end Source.IndexedAt

namespace Source.TotalRelContract

/-- Preserve an arbitrary heap-only predicate alongside an existing total
contract. `depends` says precisely which cells determine that predicate;
`unchanged` is a frame for the same safe run under the original precondition.
The original relational postcondition and execution are retained unchanged. -/
theorem frame_heap {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q : State w → State w → Prop}
    (h : TotalRelContract program heapLimit depth stmt P Q)
    (observed writes : Set (Word w)) (F : (Word w → Word w) → Prop)
    (depends : ∀ before after, Set.EqOn after before observed → F before → F after)
    (hdisjoint : Disjoint observed writes)
    (unchanged : ∀ entry finish, P entry →
      SafeExec program heapLimit depth stmt entry finish → Q entry finish →
      Set.EqOn finish.mem entry.mem writesᶜ) :
    TotalRelContract program heapLimit depth stmt
      (fun s => P s ∧ F s.mem)
      (fun entry finish => Q entry finish ∧ F finish.mem) := by
  intro entry ⟨hp, hf⟩
  obtain ⟨finish, execution, post⟩ := h entry hp
  have preserved : Set.EqOn finish.mem entry.mem observed :=
    Set.EqOn.mono (fun _ hi => hdisjoint.notMem_of_mem_left hi)
      (unchanged entry finish hp execution post)
  exact ⟨finish, execution, post, depends entry.mem finish.mem preserved hf⟩

end Source.TotalRelContract
end Ram
