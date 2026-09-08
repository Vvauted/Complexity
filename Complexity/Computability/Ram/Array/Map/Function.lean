/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Map.Correctness
import Complexity.Computability.Ram.Verification.Function.Typed

/-!
# Typed correctness of in-place array mapping

An array reference is the input and `Unit` is the actual return value. The
postcondition describes the modified contents by ordinary `List.map`, retains
the outside-array frame and preserves I/O. Function entry and return use the
existing parameter binding and shared-state restoration rules.

Only words in the represented input list require the helper's contract.
Neither correctness nor termination requires a proposed instruction bound.
-/

namespace Ram.Source.Array.Map

/-- The statically linked map transforms a borrowed array in place.
The helper implements `transform` on the original elements and preserves shared
state; the map's real stores produce the represented output and its frame. -/
theorem typed_contract {program : Program} {helper : Func} {fn heapLimit depth : Nat}
    {xs : List (Word w)} {transform : Word w → Word w}
    (hw : 0 < w) (lookup : program[fn]? = some helper)
    (correct : ∀ x ∈ xs, FunctionContract program heapLimit depth helper
      (fun args _ => args = [x])
      (fun _ entry value finish => value = [transform x] ∧ finish = entry)) :
    TypedFunctionContract program heapLimit (depth + 1) (function fn) .unit ArrayRef.args
      (fun array entry => array.Rep heapLimit xs entry)
      (fun array entry _ finish => array.Rep heapLimit (xs.map transform) finish ∧
        ArrayFrame array.base xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  apply TypedFunctionContract.of_wp rfl (fun _ _ _ => rfl) (by change 2 ≤ 7; decide)
  intro array entry represented
  obtain ⟨finish, execution, result, frame, input, output⟩ :=
    code_total_contract hw lookup correct (entry.enter array.args)
      ⟨represented.2, by simp [ArrayRef.args], by simpa [ArrayRef.args] using represented.1⟩
  refine ⟨finish, execution, by simp [function], ?_⟩
  exact ⟨⟨by simpa only [List.length_map] using represented.1, result⟩, frame, input, output⟩

end Ram.Source.Array.Map
