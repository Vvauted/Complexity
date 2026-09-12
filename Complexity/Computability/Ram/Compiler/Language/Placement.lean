/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.Set.Function
import Mathlib.Logic.Function.Basic
import Complexity.Language.Rooted
import Complexity.Computability.Ram.Compiler.Language.Heap
import Complexity.Computability.Ram.Compiler.Language.Layout

/-!
# Stable placement of existing source objects

Placement agreement is ordinary equality of functions on the existing object
identifiers. It transports descriptors, value fields, parameter words and
register correspondence without moving a RAM cell. Rootedness is enough: the
view may have a wrong type, invalid extent, or a wrapping unused address.
Source value ranges and the existing fixed-placement heap interface are
unchanged. Updating placement at a fresh identifier preserves every old root;
the update itself is proof-level data, not an allocator implementation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

namespace Placement

/-- Two placements agree at every existing object identifier. -/
def Agrees (heap : Complexity.Language.Heap) (left right : Nat → Word w) : Prop :=
  Set.EqOn left right (Set.Iio heap.objects.size)

namespace Agrees

variable {heap : Complexity.Language.Heap} {left middle right : Nat → Word w}

/-- A placement agrees with itself on the complete object domain. -/
theorem refl (heap : Complexity.Language.Heap) (placement : Nat → Word w) :
    Agrees heap placement placement := Set.eqOn_refl _ _

/-- Agreement can be used in either direction. -/
theorem symm (agreed : Agrees heap left right) : Agrees heap right left :=
  Set.EqOn.symm agreed

/-- Successive agreements retain the same addresses for existing objects. -/
theorem trans (first : Agrees heap left middle) (second : Agrees heap middle right) :
    Agrees heap left right := Set.EqOn.trans first second

/-- Agreement on a larger object domain covers every earlier object. -/
theorem mono {initial finish : Complexity.Language.Heap}
    (agreed : Agrees finish left right) (size : initial.objects.size ≤ finish.objects.size) :
    Agrees initial left right :=
  fun _ bound => agreed (Nat.lt_of_lt_of_le bound size)

/-- Compose placement extensions across the actual growth of the source heap. -/
theorem trans_of_shape {initial finish : Complexity.Language.Heap}
    (first : Agrees initial left middle) (second : Agrees finish middle right)
    (growth : initial.ShapeExtends finish) : Agrees initial left right :=
  first.trans (second.mono growth.size_le)

/-- Retained views keep both descriptor fields, even when access would fail. -/
theorem bufferRef (agreed : Agrees heap left right) {τ : CellTy} {buffer : Buffer τ}
    (rooted : buffer.Rooted heap) :
    LanguageCompiler.bufferRef left buffer = LanguageCompiler.bufferRef right buffer := by
  simp only [LanguageCompiler.bufferRef, agreed rooted]

/-- Stored tail links use their actual retained placements. Backward links make
all referenced identifiers part of the same existing object domain. -/
theorem heapObjectWords {heapLimit : Nat} {target : Source.State w}
    (agreed : Agrees heap left right) (represented : HeapRep left heapLimit heap target)
    {object : Nat} {stored : HeapObject} (found : heap.objects[object]? = some stored) :
    LanguageCompiler.heapObjectWords left stored =
      LanguageCompiler.heapObjectWords right stored := by
  cases stored with
  | buffer kind values => rfl
  | node kind head tail =>
      cases tail with
      | none => rfl
      | some tail =>
          have older := represented.backward (Heap.node?_eq_some_iff.mpr found)
          have present := (Array.getElem?_eq_some_iff.mp found).choose
          simp only [LanguageCompiler.heapObjectWords, agreed (older.trans present)]

/-- Agreement preserves the mathematical observation of each actual field. -/
theorem valueField (agreed : Agrees heap left right) {τ : Ty} {value : Value τ}
    (rooted : ValueRooted heap value) (i : Fin (fieldCount τ)) :
    LanguageCompiler.valueField left value i = LanguageCompiler.valueField right value i := by
  induction τ with
  | nat | bool => rfl
  | unit => exact Fin.elim0 i
  | buffer kind | node kind =>
      simp only [LanguageCompiler.valueField, agreed rooted]
  | prod first second ihFirst ihSecond =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [LanguageCompiler.valueField_prod_left] using ihFirst rooted.1 j
      · intro j
        simpa only [LanguageCompiler.valueField_prod_right] using ihSecond rooted.2 j
  | option τ ih =>
      cases value with
      | none => rfl
      | some value =>
          refine Fin.cases rfl ?_ i
          intro j
          simpa only [LanguageCompiler.valueField_some_succ] using ih rooted j

/-- All emitted argument or result words retain their original encodings. -/
theorem valueWords (agreed : Agrees heap left right) {τ : Ty} {value : Value τ}
    (rooted : ValueRooted heap value) :
    LanguageCompiler.valueWords left value = LanguageCompiler.valueWords right value := by
  unfold LanguageCompiler.valueWords
  congr 1
  funext i
  rw [agreed.valueField rooted i]

/-- A caller's complete parameter encoding survives placement extension. -/
theorem envWords (agreed : Agrees heap left right) {Γ : List Ty} {env : Env Γ}
    (rooted : env.Rooted heap) :
    LanguageCompiler.envWords left env = LanguageCompiler.envWords right env := by
  induction Γ with
  | nil => rfl
  | cons τ Γ ih =>
      simp only [LanguageCompiler.envWords]
      rw [agreed.valueWords rooted.head, ih rooted.tail]

end Agrees

/-- Installing an address at an unused identifier changes no existing placement.
Taking the identifier to be the old object count is the fresh append case. -/
theorem agrees_update (heap : Complexity.Language.Heap) (placement : Nat → Word w)
    {object : Nat} (fresh : heap.objects.size ≤ object) (address : Word w) :
    Agrees heap placement (Function.update placement object address) := by
  intro other bound
  exact (Function.update_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound fresh))
    address placement).symm

end Placement

/-- Placement transport preserves exact register matching without changing the
registers or strengthening source scalar and buffer-length range conditions. -/
theorem RegisterMap.Matches.placement {heap : Complexity.Language.Heap}
    {left right : Nat → Word w} {layout : RegisterMap Γ} {env : Env Γ}
    {regs : Reg → Word w} (matched : layout.Matches left env regs)
    (agreed : Placement.Agrees heap left right) (rooted : env.Rooted heap) :
    layout.Matches right env regs := by
  intro τ v i
  exact (matched v i).trans (agreed.valueField (rooted v) i)

/-- Complete representation of the same heap is independent of placement on
unallocated identifiers. No memory contents, ranges or separation facts change. -/
theorem HeapRep.placement {heap : Complexity.Language.Heap} {left right : Nat → Word w}
    {target : Source.State w} (represented : HeapRep left heapLimit heap target)
    (agreed : Placement.Agrees heap left right) : HeapRep right heapLimit heap target := by
  refine ⟨?_, represented.fit, ?_, represented.backward⟩
  · intro object stored found
    rw [← agreed (Array.getElem?_eq_some_iff.mp found).choose,
      ← agreed.heapObjectWords represented found]
    exact represented.stored found
  · intro object other stored otherStored found foundOther different
      index bound otherIndex otherBound
    rw [← agreed (Array.getElem?_eq_some_iff.mp found).choose,
      ← agreed (Array.getElem?_eq_some_iff.mp foundOther).choose]
    exact represented.disjoint found foundOther different index
      (by simpa only [agreed.heapObjectWords represented found] using bound) otherIndex
      (by simpa only [agreed.heapObjectWords represented foundOther] using otherBound)

end Ram.LanguageCompiler
