/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Examples.Language.Traversal

/-!
# Sequential calls on disjoint borrowed buffers

The source function calls the existing traversal twice on the same shared heap.
Its native proof uses only the supplied function contracts: the first call's
frame preserves the second input, and the second call's frame preserves the
first result. Views disjoint from both buffers keep their initial contents.
No traversal body or second implementation is unfolded here.
-/

namespace Complexity.Language.Examples.Traversal

open scoped Std.Do Part.TotalCorrectness

/-- Two ordinary calls compose their array results and heap frames, including
when the disjoint buffers are borrowed slices of one shared object. -/
theorem boundedMapPair_spec (xs ys : Buffer .nat) (limit : Nat)
    (leftContents rightContents : Array Nat) (initial : Heap)
    (separated : xs.Disjoint ys) :
    ⦃fun heap => ⌜heap = initial ∧ xs.Contents heap leftContents ∧
      ys.Contents heap rightContents⌝⦄
      Implementation.boundedMapPair xs ys limit
    ⦃⇓ _ finish => ⌜xs.Contents finish (leftContents.map fun x => min (x + 1) limit) ∧
        ys.Contents finish (rightContents.map fun x => min (x + 1) limit) ∧
        ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
          xs.Disjoint other → ys.Disjoint other →
            other.Contents initial contents → other.Contents finish contents⌝⦄ := by
  have leftSpec := Implementation.boundedMap_spec (boundedMap_total_frame leftContents) xs limit
  have rightSpec := Implementation.boundedMap_spec (boundedMap_total_frame rightContents) ys limit
  rw [Implementation.boundedMapPair_eq]
  mvcgen [leftSpec]
  rename_i heap input
  rcases input with ⟨same, observedLeft, observedRight⟩
  subst heap
  refine ⟨observedLeft, ?_⟩
  intro value middle mappedLeft frameLeft
  mvcgen [rightSpec]
  refine ⟨frameLeft ys rightContents separated observedRight, ?_⟩
  intro value finish mappedRight frameRight
  mvcgen
  refine ⟨frameRight xs _ separated.symm mappedLeft, mappedRight, ?_⟩
  intro kind other contents outsideLeft outsideRight observed
  exact frameRight other contents outsideRight (frameLeft other contents outsideLeft observed)

/-- The same two calls terminate with both mapped arrays in their actual final
heap, preserving every initial observation outside both borrowed views. -/
theorem boundedMapPair_eval (xs ys : Buffer .nat) (limit : Nat)
    {leftContents rightContents : Array Nat} {heap : Heap}
    (observedLeft : xs.Contents heap leftContents)
    (observedRight : ys.Contents heap rightContents) (separated : xs.Disjoint ys) :
    ∃ finish, Implementation.boundedMapPair xs ys limit heap = Part.some (.ok (), finish) ∧
      xs.Contents finish (leftContents.map fun x => min (x + 1) limit) ∧
      ys.Contents finish (rightContents.map fun x => min (x + 1) limit) ∧
      ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
        xs.Disjoint other → ys.Disjoint other →
          other.Contents heap contents → other.Contents finish contents := by
  obtain ⟨value, finish, executed, mappedLeft, mappedRight, frame⟩ :=
    (triple_iff_eval _ _ _).mp
      (boundedMapPair_spec xs ys limit leftContents rightContents heap separated)
      heap ⟨rfl, observedLeft, observedRight⟩
  exact ⟨finish, executed, mappedLeft, mappedRight, frame⟩

/-- The composed function exposes the same ordinary two-array result and
outside-both frame through its generated named argument interface. -/
theorem boundedMapPair_total (leftContents rightContents : Array Nat) :
    Implementation.boundedMapPair_contract
      (fun xs ys _ heap => xs.Contents heap leftContents ∧
        ys.Contents heap rightContents ∧ xs.Disjoint ys)
      (fun xs ys limit initial _ finish =>
        xs.Contents finish (leftContents.map fun x => min (x + 1) limit) ∧
        ys.Contents finish (rightContents.map fun x => min (x + 1) limit) ∧
        ∀ {kind : CellTy} (other : Buffer kind) (contents : Array (CellValue kind)),
          xs.Disjoint other → ys.Disjoint other →
            other.Contents initial contents → other.Contents finish contents) := by
  apply (Implementation.boundedMapPair_total_iff _ _).mpr
  rintro xs ys limit heap ⟨observedLeft, observedRight, separated⟩
  obtain ⟨finish, executed, mappedLeft, mappedRight, frame⟩ :=
    boundedMapPair_eval xs ys limit observedLeft observedRight separated
  exact ⟨(), finish, executed, mappedLeft, mappedRight, frame⟩

end Complexity.Language.Examples.Traversal
