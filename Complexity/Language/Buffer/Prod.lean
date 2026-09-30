/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation.Array
import Complexity.Language.Eval.Basic

/-!
# Reading arrays of scalar pairs

One pair array uses two scalar-buffer views. The source body projects both
handles, performs two actual indexed reads, and constructs the returned pair.
The theorem observes an ordinary `Array` of pairs, not two unrelated arrays or
an external decoder. Reads preserve the complete heap and allow aliases.

This is a reusable operation of the existing typed core. Fixed program input
layouts and represented frontend selection are separate integration work.
-/

namespace Complexity.Language.Buffer.Prod

/-- Two column handles are passed together, followed by the row index. -/
def params (left right : CellTy) : List Ty :=
  [.prod (.buffer left) (.buffer right), .nat]

/-- Actual typed source instructions for two column reads and one pair result. -/
def readBody (left right : CellTy) {signatures : List Signature} :
    Stmt signatures (params left right) (.prod left.toTy right.toTy) :=
  .letPrim (.fst (.var .here))
    (.letPrim (.snd (.var (.there .here)))
      (.read (.var (.there .here)) (.var (.there (.there (.there .here))))
        (.read (.var (.there .here)) (.var (.there (.there (.there (.there .here)))))
          (.letPrim (.pair (.var (.there .here)) (.var .here))
            (.ret (.var .here))))))

/-- The input and output types of the actual source function. -/
abbrev signatures (left right : CellTy) : List Signature :=
  [⟨params left right, .prod left.toTy right.toTy⟩]

/-- The sole entry in the pair-read family. -/
abbrev readId (left right : CellTy) : Fin (signatures left right).length :=
  ⟨0, by simp [signatures]⟩

/-- A source program, with no native callback or separately chosen evaluator. -/
def program (left right : CellTy) : Program (signatures left right) where
  body fn := by
    have same : fn = readId left right := by
      apply Fin.ext
      have bound := fn.isLt
      simp only [signatures, List.length_cons, List.length_nil] at bound
      change fn.val = 0
      omega
    subst fn
    exact readBody left right

/-- Finite execution follows the two reads at the same unchanged heap. -/
theorem read_exec {left right : CellTy} {signatures : List Signature}
    (source : Program signatures) (columns : Buffer left × Buffer right)
    (index : Nat) (heap : Heap) (first : CellValue left) (second : CellValue right)
    (firstRead : heap.read columns.1 index = .ok first)
    (secondRead : heap.read columns.2 index = .ok second) :
    Exec source (readBody left right)
      ⟨Env.cons columns (Env.cons index Env.empty), heap⟩
      ⟨Env.cons columns (Env.cons index Env.empty), heap⟩
      (.returned (left.toValue first, right.toValue second)) := by
  let entry : State (params left right) :=
    ⟨Env.cons columns (Env.cons index Env.empty), heap⟩
  let firstColumn := State.cons (τ := .buffer left) columns.1 entry
  let bothColumns := State.cons (τ := .buffer right) columns.2 firstColumn
  let firstValue := State.cons (τ := left.toTy) (left.toValue first) bothColumns
  let bothValues := State.cons (τ := right.toTy) (right.toValue second) firstValue
  refine Exec.letPrim (finish := firstColumn) ?_
  refine Exec.letPrim (finish := bothColumns) ?_
  refine Exec.read (finish := firstValue) firstRead ?_
  refine Exec.read (finish := bothValues) secondRead ?_
  exact Exec.letPrim (Exec.ret _ _)

/-- An in-bounds row read returns the ordinary array's pair, preserving all
storage, even when the column views alias. -/
theorem read_eval {left right : CellTy}
    (xs : Array (CellValue left × CellValue right))
    (columns : Buffer left × Buffer right) (index : Nat) (heap : Heap)
    (observed : (Representation.arrayProd (Representation.array left)
      (Representation.array right)).Rel xs columns heap) (bound : index < xs.size) :
    (program left right).eval (readId left right)
      (Env.cons columns (Env.cons index Env.empty)) heap =
        Part.some (.ok (left.toValue xs[index].1, right.toValue xs[index].2), heap) := by
  change columns.1.Contents heap (xs.map Prod.fst) ∧
    columns.2.Contents heap (xs.map Prod.snd) at observed
  apply Program.eval_eq_ok_iff.mpr
  refine ⟨⟨Env.cons columns (Env.cons index Env.empty), heap⟩, ?_, rfl⟩
  apply read_exec
  · exact (observed.1.read (by simpa using bound)).trans
      (congrArg Except.ok (Array.getElem_map Prod.fst (by simpa using bound)))
  · exact (observed.2.read (by simpa using bound)).trans
      (congrArg Except.ok (Array.getElem_map Prod.snd (by simpa using bound)))

end Complexity.Language.Buffer.Prod
