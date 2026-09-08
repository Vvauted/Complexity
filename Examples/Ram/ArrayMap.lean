/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Map.Function
import Complexity.Computability.Ram.Array.Map.Time
import Complexity.Computability.Ram.Array.Model
import Complexity.Computability.Ram.Source.Function.Linking
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Tactic.Ram.Run
import Examples.Ram.LocalBindings

/-!
# In-place mapping with an imported helper

The named source calls the already verified square function and writes each
result back into the borrowed array. The shared map contract supplies the loop
invariant, termination and outside-array frame; the client supplies only the
helper contract and its ordinary mathematical transformation.

The executable contents equation uses `List.map`. Its independent full-run bound
includes the helper calls, real loads and stores, both iteration cursors, the
explicit source index, and the enclosing call and halt. No list loader or
allocation is performed, and machine-word multiplication remains modular.
-/

namespace Ram.Examples.ArrayMap

open Source Source.Array

/-- Transform a borrowed array using a statically imported source function. -/
ram_def functions := ram_functions% {
  include LocalBindings.functions as Scalar;
  fn mapSquares(xs : array) : Unit {
    let mut i := 0;
    for x in xs {
      let y ← call Scalar.square(x);
      xs[i] := y;
      i += 1;
    }
    return;
  }
}

/-- The named source is an instance of the verified reusable map operation. -/
theorem mapSquares_eq :
    functions.function.mapSquares = Map.function functions.functionIndex.Scalar.square := rfl

/-- Ordinary list mapping describes the actual mutation. The helper's contract
is reused without inspecting its body or exposing the traversal's local slots. -/
theorem typed_contract {heapLimit : Nat} {xs : List (Word w)} (hw : 0 < w) :
    TypedFunctionContract functions.program heapLimit 1 functions.function.mapSquares
      .unit functions.arguments.mapSquares
      (fun array entry => array.Rep heapLimit xs entry)
      (fun array entry _ finish => array.Rep heapLimit (xs.map (fun x => x * x)) finish ∧
        ArrayFrame array.base xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  rw [mapSquares_eq]
  exact Map.typed_contract hw functions.function_lookup.Scalar.square
    (fun x _ => (LocalBindings.square_contract heapLimit x).renameCalls functions.embeds.Scalar)

/-- A separate uniform bound on the same function body. Squaring has an empty
body and computes its result in the actual return expression, charged by its call. -/
theorem function_timeBound {w control heapLimit : Nat} (hw : 0 < w) (array : ArrayRef w) :
    FunctionTimeBound control functions.program heapLimit 1 functions.function.mapSquares
      (fun args _ => args = functions.arguments.mapSquares array)
      (fun _ _ => 46 * array.length.toNat + 8) := by
  have helperTime : FunctionTimeBound (w := w) control functions.program heapLimit 0
      functions.function.Scalar.square (fun args _ => args.length = 1) (fun _ _ => 0) := by
    apply FunctionTimeBound.of_body_at
    intro args entry _
    exact TimeBound.skip _
  rw [mapSquares_eq]
  have time := Map.function_timeBound hw functions.function_lookup.Scalar.square helperTime array
  simpa [ABI.callPrefixLocals_length_eq, ABI.returnCodeResultsLocals_length,
    LocalBindings.functions.result_eq.square, Func.renameCalls, Expr.compile] using time

variable {heapLimit : Nat} {array : ArrayRef 32} {xs : List (Word 32)}
  {entry : Source.State 32}

/-- Budget-free correctness proves normal termination of the actual compiled
call, with the two required frames and no separately supplied time bound. -/
theorem halts (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts functions.registers functions.program
      functions.functionIndex.mapSquares functions.function.mapSquares.params heapLimit
      (functions.arguments.mapSquares array) entry := by
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (contract := typed_contract (by decide : 0 < 32)) (pre := represented))
    [functions.function_lookup.mapSquares]
  exact hstack

/-- The ordinary executable state projection contains exactly the mathematical
mapped list. This is the compiled invocation, not a host call to `List.map`. -/
theorem applyState_contents (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    let finish := (functions.applyState.mapSquares array heapLimit entry
      (halts represented hstack)).2
    arrayContents finish.mem array.base xs.length = xs.map (fun x => x * x) := by
  have post := by
    ram_run_apply (LocalCompiler.Function.applyStateTyped_spec
      (shape := functions.results_length.mapSquares)
      (h := halts represented hstack)
      (contract := typed_contract (by decide : 0 < 32)) (pre := represented))
      [functions.function_lookup.mapSquares]
    exact hstack
  have contents := post.1.2.1.contents_eq
  simpa only [List.length_map] using contents

/-- Bound this same complete invocation, including its outer call and halt. -/
theorem runTotal_steps_le (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + 2 * ABI.frameSize functions.registers < 2 ^ 32) :
    (functions.runTotal.mapSquares array heapLimit entry (halts represented hstack)).steps ≤
      46 * xs.length + 71 := by
  obtain ⟨value, finish, execution, _⟩ := typed_contract (by decide : 0 < 32) array entry represented
  change (LocalCompiler.Function.runTotal functions.registers functions.program
    functions.functionIndex.mapSquares functions.function.mapSquares.params heapLimit
    (functions.arguments.mapSquares array) entry (halts represented hstack)).steps ≤ _
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (h := halts represented hstack) (execution := execution)
    (time := function_timeBound (by decide : 0 < 32) array) (pre := rfl))
    [functions.function_lookup.mapSquares, functions.result_eq.mapSquares, represented.1]
  exact hstack

end Ram.Examples.ArrayMap
