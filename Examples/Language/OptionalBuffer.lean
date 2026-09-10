/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Std.Tactic.Do

/-!
# Imported structured results with an optional borrowed buffer

A pure metadata helper classifies a length. An independently declared library
uses that actual result to return either no buffer or a full borrowed slice.
The client matches the imported optional handle, reads and increments its first
cell only when present, and returns the structured result. Products and options
here are source values carried by actual calls, not a host-side substitute for
the source implementations.

Correctness is stated with ordinary arrays and preservation of outside views.
`OptionalBufferCompiled` connects these same implementations to RAM execution.
-/

namespace Complexity.Language.Examples.OptionalBuffer

open scoped Std.Do Part.TotalCorrectness

source_program (pure) Metadata where
  def classifyLength (n : Nat) : Option (Nat × Nat) := do
    if n == 0 then
      return none
    else
      return some (n, 0)

source_program Library importing Metadata where
  def inspect (xs : Buffer Nat) : Nat × Option (Buffer Nat) := do
    let summary ← Metadata.classifyLength xs.length
    match summary with
    | none => return (0, none)
    | some bounds =>
      let view ← xs.slice bounds.2 bounds.1
      return (bounds.1, some view)

source_program Implementation importing Library where
  def bump (xs : Buffer Nat) : Nat × Option (Buffer Nat) := do
    let info ← Library.inspect xs
    match info.2 with
    | none => return (info.1, none)
    | some view =>
      let head ← view.get 0
      view.set 0 (head + 1)
      return (info.1, some view)

/-- The library returns the original borrowed handle exactly when nonempty. -/
def inspectResult (xs : Buffer .nat) : Nat × Option (Buffer .nat) :=
  (xs.length, if xs.length = 0 then none else some xs)

/-- The ordinary mathematical update of the first element, if any. -/
def bumped (contents : Array Nat) : Array Nat :=
  contents.modify 0 (· + 1)

/-- The returned handle and all array/frame properties refer to the same final heap. -/
def bumpPost (xs : Buffer .nat) (contents : Array Nat) (initial : Heap)
    (result : Nat × Option (Buffer .nat)) (finish : Heap) : Prop :=
  result = inspectResult xs ∧ xs.Contents finish (bumped contents) ∧
    xs.PreservesOutside initial finish

/-- The pure source helper has an ordinary optional-pair result. -/
theorem classifyLength_eq (n : Nat) :
    Metadata.classifyLength n = if n = 0 then none else some (n, 0) := by
  by_cases empty : n = 0 <;>
    simp [Metadata.classifyLength, Id.run, Id.instMonad, empty]

/-- Generated correspondence transfers the same pure result to source execution. -/
theorem classifyLength_total :
    Metadata.classifyLength_contract (fun _ _ => True)
      (fun n heap value finish =>
        value = (if n = 0 then none else some (n, 0)) ∧ finish = heap) := by
  simpa only [classifyLength_eq] using Metadata.classifyLength_total

/-- The imported classifier selects the actual full slice without changing the heap. -/
theorem inspect_eval (xs : Buffer .nat) :
    Library.inspect xs =
      (pure (inspectResult xs) : ExceptT Fault (StateT Heap Part)
        (Nat × Option (Buffer .nat))) := by
  rw [Library.inspect_eq]
  dsimp only
  rw [Metadata.classifyLength_action_eq_pure, classifyLength_eq]
  have slice : xs.sliceM 0 xs.length =
      (pure xs : ExceptT Fault (StateT Heap Part) (Buffer .nat)) := by
    funext heap
    exact Buffer.sliceM_eq_ok xs.slice_self heap
  by_cases empty : xs.length = 0 <;> simp [inspectResult, empty, slice]

/-- Inspecting metadata terminates even for an empty view, without reading its cells. -/
theorem inspect_total :
    Library.inspect_contract (fun _ _ => True)
      (fun xs heap result finish => result = inspectResult xs ∧ finish = heap) := by
  apply (Library.inspect_total_iff _ _).mpr
  intro xs heap _
  exact ⟨inspectResult xs, heap, congrFun (inspect_eval xs) heap, rfl, rfl⟩

/-- The client's native proof uses the imported result and the ordinary buffer
read/write contracts; the resulting frame concerns the actual write heap. -/
theorem bump_spec (xs : Buffer .nat) (contents : Array Nat) (heap : Heap)
    (observed : xs.Contents heap contents) :
    ⦃fun entry => ⌜entry = heap⌝⦄ Implementation.bump xs
    ⦃⇓ result finish => ⌜bumpPost xs contents heap result finish⌝⦄ := by
  rw [Implementation.bump_eq, inspect_eval]
  by_cases empty : xs.length = 0
  · simp only [inspectResult, empty, if_true, pure_bind]
    apply Std.Do.Triple.pure
    intro finish same
    subst finish
    have size : contents.size = 0 := observed.size_eq.trans empty
    refine ⟨?_, ?_, Buffer.PreservesOutside.refl xs heap⟩
    · simp [inspectResult, empty]
    · simpa [bumped, Array.modify, Array.modifyM, size, Id.run, Id.instMonad]
        using observed
  · have bound : 0 < contents.size := by rw [observed.size_eq]; omega
    simp only [inspectResult, empty, if_false, pure_bind]
    mvcgen
    rename_i entry same
    subst entry
    refine ⟨contents, bound, observed, ?_⟩
    mvcgen
    refine ⟨contents, bound, observed, ?_⟩
    intro finish written updated
    mvcgen
    refine ⟨?_, ?_, fun {kind : CellTy} =>
      Buffer.PreservesOutside.write written (σ := kind)⟩
    · simp [inspectResult, empty]
    · simpa [bumped, Array.modify, Array.modifyM, bound, Id.run, Id.instMonad]
        using updated

/-- Source correctness in ordinary parameters: the returned optional handle,
updated native array and outside-view frame share one real final heap. -/
theorem bump_total (contents : Array Nat) :
    Implementation.bump_contract (fun xs heap => xs.Contents heap contents)
      (fun xs heap result finish => bumpPost xs contents heap result finish) := by
  apply (Implementation.bump_total_iff _ _).mpr
  intro xs heap observed
  exact (triple_iff_eval _ _ _).mp (bump_spec xs contents heap observed) heap rfl

end Complexity.Language.Examples.OptionalBuffer
