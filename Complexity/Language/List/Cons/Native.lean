/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Cons

/-!
# Native observations of the actual allocating list constructor

`consEval` binds ordinary head and node-handle arguments to the existing
`List.Cons.program` entry. Its mathematical result is observed in the actual
extended heap, not through a pure encoding or an equivalence for lists.

`eval_exists` reuses the shared source total-correctness theorem. The returned
`Heap.ShapeExtends` proof transports any old list observation to the real
intermediate heap with `Representation.list_mono`, including shared tails.
Ordinary exception/state bind then passes that heap to the next source action.
-/

namespace Complexity.Language.List.Cons

/-- Invoke the existing allocating source entry with its actual head and tail.
This is argument binding of `Program.eval`, not another list implementation. -/
noncomputable def consEval (kind : CellTy) (head : CellValue kind)
    (root : Option (NodeRef kind)) :
    ExceptT Fault (StateT Heap Part) (Option (NodeRef kind)) :=
  (program kind).eval (entry kind)
    (Env.cons (kind.toValue head) (Env.cons root Env.empty))

/-- The real allocation returns the mathematical cons in its actual final
heap. Every previously observed immutable list can be reused in that heap;
the theorem does not restore the initial heap or require a unique list encoding. -/
theorem eval_exists (kind : CellTy) (head : CellValue kind)
    (values : List (CellValue kind)) (root : Option (NodeRef kind)) (heap : Heap)
    (observed : (Representation.list kind).Rel values root heap) :
    ∃ returned finish,
      consEval kind head root heap = Part.some (.ok returned, finish) ∧
      (Representation.list kind).Rel (head :: values) returned finish ∧
      heap.ShapeExtends finish := by
  obtain ⟨returned, finish, evaluated, related, _, _, preserved⟩ :=
    (total kind head values).eval_spec
      (args := Env.cons (kind.toValue head) (Env.cons root Env.empty))
      (initialHeap := heap) ⟨by simp, observed⟩
  exact ⟨returned, finish, evaluated, related, preserved⟩

end Complexity.Language.List.Cons
