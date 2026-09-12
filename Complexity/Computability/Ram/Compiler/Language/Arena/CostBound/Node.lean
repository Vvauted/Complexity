/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound

/-!
# Arena costs of selected options and actual node reads

These rules retain the source selection and lookup equations. The continuation
uses the actual stored payload, and its cost is observed on the same execution.
Neither a lookup nor a word-range condition is asserted by the budget itself.
-/

namespace Ram.LanguageCompiler.StmtArenaCostBound

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
variable {entry : Complexity.Language.State Γ} {bound : Nat}

/-- A known absent option charges only its actual absent branch. -/
theorem match_none {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = none)
    (body : StmtArenaCostBound program w heapLimit depth noneBranch entry bound) :
    StmtArenaCostBound program w heapLimit depth (.matchOption value noneBranch someBranch)
      entry (bound + 2) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | matchNone tail => exact Nat.add_le_add_right (body _ _ tail) 2
  | matchSome tail =>
      have impossible : none = some _ := selected.symm.trans (by assumption)
      cases impossible

/-- A known present option retains its actual payload and emitted field copies. -/
theorem match_some {τ : Ty} {value : Atom Γ (.option τ)} {payload : Value τ}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = some payload)
    (body : StmtArenaCostBound program w heapLimit depth someBranch
      (Complexity.Language.State.cons payload entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.matchOption value noneBranch someBranch)
      entry (2 * fieldCount τ + bound + 3) := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | matchNone tail =>
      have impossible : some payload = none := selected.symm.trans (by assumption)
      cases impossible
  | matchSome tail =>
      have same : some payload = some _ := selected.symm.trans (by assumption)
      cases Option.some.inj same
      exact Nat.add_le_add_right (Nat.add_le_add_left (body _ _ tail) _) 3

/-- Each node-read continuation is bounded at the actual stored head and tail.
The combining inequality may depend on both returned fields. -/
theorem readNode {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    {nextBound : CellValue kind → Option (NodeRef kind) → Nat}
    (body : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) entry) (nextBound head tail))
    (combine : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      readNodeCodeSize + nextBound head tail ≤ bound) :
    StmtArenaCostBound program w heapLimit depth (.readNode ref continuation) entry bound := by
  intro finish control execution cursor finalCursor ready steps cost
  cases cost with
  | readNode tail =>
      exact (Nat.add_le_add_left (body _ _ (by assumption) _ _ tail) _).trans
        (combine _ _ (by assumption))

/-- A fixed continuation bound may still use the actual successful lookup. -/
theorem readNode_of_success {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    (body : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      StmtArenaCostBound program w heapLimit depth continuation
        (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) entry) bound) :
    StmtArenaCostBound program w heapLimit depth (.readNode ref continuation)
      entry (readNodeCodeSize + bound) :=
  readNode (nextBound := fun _ _ => bound) body (fun _ _ _ => Nat.le_refl _)

end Ram.LanguageCompiler.StmtArenaCostBound
