/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Verification

/-!
# Source recursion through mathematical function contracts

Well-founded induction presents smaller mathematical indices as `FunctionTotal`
contracts, directly usable by `TotalWP.call`. Each body is the actual selected
source body, and its contract retains the initial and final shared heaps.

The index may select a fixed function for ordinary recursion, or different
functions for mutual recursion. Its precondition relates the mathematical index
to the actual arguments; it is not extra runtime state, fuel or a time budget.
No new execution relation or recursive interpreter is introduced.
-/

universe u

namespace Complexity.Language.FunctionTotal

/-- Verify a family of source functions by well-founded descent on mathematical
indices. The body proof receives complete callable contracts at every smaller
index, including their actual returned values and shared-heap effects. A fixed
function selector gives ordinary recursion; a varying selector also supports
mutual recursion between functions with different signatures. -/
theorem verify_wellFounded {signatures : List Signature} {program : Program signatures}
    {Arg : Type u} (fn : Arg → Fin signatures.length)
    (pre : (arg : Arg) → Env signatures[fn arg].params → Heap → Prop)
    (post : (arg : Arg) → Env signatures[fn arg].params → Heap →
      Value signatures[fn arg].result → Heap → Prop)
    {r : Arg → Arg → Prop} (wf : WellFounded r)
    (body : ∀ arg,
      (∀ smaller, r smaller arg →
        FunctionTotal program (fn smaller) (pre smaller) (post smaller)) →
      ∀ args heap, pre arg args heap →
        TotalWP program (program.body (fn arg)) (fun _ => False)
          (fun value finish => post arg args heap value finish.heap) ⟨args, heap⟩) :
    ∀ arg, FunctionTotal program (fn arg) (pre arg) (post arg) := by
  intro arg
  induction arg using wf.induction with
  | h arg ih => exact of_wp (body arg ih)

end Complexity.Language.FunctionTotal
