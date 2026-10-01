/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Arena costs of buffer reads and borrowed slices

The continuation retains the actual read or slice equation, even when it later
allocates. These rules bound the existing measured execution; they do not assert
successful access, termination, word ranges or sufficient arena capacity.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
variable {entry : Complexity.Language.State Γ} {bound : Nat}

/-- Retain the actual loaded cell in a possibly allocating continuation. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    {nextBound : CellValue kind → Nat}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) (nextBound value))
    (combine : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      readCodeSize + nextBound value ≤ bound) :
    StmtArenaCostBound program w heapLimit depth (.read buffer index continuation) entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | read tail =>
      exact (Nat.add_le_add_left (body _ (by assumption) _ _ tail) _).trans
        (combine _ (by assumption))

/-- A uniform numeric bound can still use the successful read equation. -/
theorem read_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.read buffer index continuation) entry
      (readCodeSize + bound) :=
  read (nextBound := fun _ => bound) body (fun _ _ => Nat.le_refl _)

/-- A uniform continuation does not need a separate contents contract. -/
theorem read_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value, StmtArenaCostBound program w heapLimit depth continuation
      (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.read buffer index continuation) entry
      (readCodeSize + bound) :=
  read_of_success (fun value _ => body value)

/-- A borrowed slice passes its actual descriptor, not a copied host array. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {nextBound : Buffer kind → Nat}
    (body : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons view entry) (nextBound view))
    (combine : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view → sliceCodeSize + nextBound view ≤ bound) :
    StmtArenaCostBound program w heapLimit depth (.slice buffer offset length continuation)
      entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | slice tail =>
      exact (Nat.add_le_add_left (body _ (by assumption) _ _ tail) _).trans
        (combine _ (by assumption))

/-- Retain a successful slice equation under a uniform continuation bound. -/
theorem slice_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    (body : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons view entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.slice buffer offset length continuation)
      entry (sliceCodeSize + bound) :=
  slice (nextBound := fun _ => bound) body (fun _ _ => Nat.le_refl _)

/-- Uniform slice continuations need no result observation. -/
theorem slice_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    (body : ∀ view, StmtArenaCostBound program w heapLimit depth continuation
      (Complexity.Language.State.cons view entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.slice buffer offset length continuation)
      entry (sliceCodeSize + bound) :=
  slice_of_success (fun view _ => body view)

end Ram.LanguageCompiler.StmtArenaCostBound
