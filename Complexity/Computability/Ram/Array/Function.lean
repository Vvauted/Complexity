/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Traversal
import Complexity.Computability.Ram.Source.Function.Time
import Complexity.Computability.Ram.Verification.Function.Typed

/-!
# Calling the array-copy function

`Ram.Source.Array.copy_function_contract` describes the actual named copy
function through pointers, a length and mathematical lists. Its precondition
does not mention caller registers: parameter binding and restored locals are
handled by `Ram.Source.FunctionContract`.

Both arrays must already be represented in shared memory. This is an ordinary
function contract, not a free loader or an input/output main program. The
length must fit in one word and the arrays must not overlap. Correctness and
termination use no instruction budget. The separate function time bound reuses
`Ram.Source.Array.copy_timeBound` on the same body; call-site argument and
return overhead is supplied by `Ram.Source.FunctionMeasuredExec.call`.
-/

namespace Ram.Source.Array

/-- Copy the represented source into the represented destination. No return
fields are produced; both array contents and every destination-external memory word
are described directly, without exposing the callee's parameter registers. -/
theorem copy_function_contract {w heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length) (hfit : xs.length < 2 ^ w)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length) :
    FunctionContract program heapLimit depth copyFunctions.function.copy
      (fun args entry =>
        args = copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length) ∧
        ArrayAt heapLimit source xs entry ∧ ArrayAt heapLimit destination ys entry)
      (fun _ entry value finish => value = [] ∧
        ArrayAt heapLimit source xs finish ∧ ArrayAt heapLimit destination xs finish ∧
        ArrayFrame destination xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  apply FunctionContract.of_body
    (R := CopyPre heapLimit source destination xs ys)
    (S := CopyPost heapLimit source destination xs)
  · intro entered pre
    obtain ⟨callee, execution, result⟩ :=
      copy_total_contract (program := program) (depth := depth) hw hlen hdisjoint entered pre
    exact ⟨callee, execution, by simp [copyFunctions.result_eq.copy], result⟩
  · rintro args entry ⟨rfl, _, _⟩
    exact copyFunctions.arguments_length.copy source destination (BitVec.ofNat w xs.length)
  · decide
  · rintro args entry ⟨rfl, sourceArray, destinationArray⟩
    refine ⟨sourceArray, destinationArray, rfl, rfl, ?_⟩
    exact Word.ofNat_toNat_of_lt hfit
  · intro args entry pre callee result
    exact ⟨rfl, result.source_array, result.destination_array, result.frame,
      result.input, result.output⟩

/-- The existing copy implementation returns genuine `Unit`; its typed view
retains the original array domain and actual shared-memory postcondition. -/
theorem copy_function_typed_contract {w heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (sameLength : ys.length = xs.length) (fit : xs.length < 2 ^ w)
    (disjoint : ArraysDisjoint source xs.length destination xs.length) :
    TypedFunctionContract program heapLimit depth copyFunctions.function.copy .unit
      (fun input : Word w × Word w × Word w =>
        copyFunctions.arguments.copy input.1 input.2.1 input.2.2)
      (fun input entry => input = (source, destination, BitVec.ofNat w xs.length) ∧
        ArrayAt heapLimit source xs entry ∧ ArrayAt heapLimit destination ys entry)
      (fun _ entry _ finish =>
        ArrayAt heapLimit source xs finish ∧ ArrayAt heapLimit destination xs finish ∧
        ArrayFrame destination xs.length entry.mem finish.mem ∧
        finish.input = entry.input ∧ finish.outputRev = entry.outputRev) := by
  apply TypedFunctionContract.of_raw copyFunctions.results_length.copy
    (copy_function_contract hw sameLength fit disjoint)
  · rintro _ _ ⟨rfl, sourceArray, destinationArray⟩
    exact ⟨rfl, sourceArray, destinationArray⟩
  · intro _ _ _ _ _ result
    exact result.2

/-- Invoke copy on existing arrays, without an entry point, input stream or
destination register or dummy return word. The resulting heap contains
the original list at both pointers. Caller locals are restored by the
invocation relation, not an additional premise of this theorem. -/
theorem copy_function_runs {w heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length) (hfit : xs.length < 2 ^ w)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (entry : State w) (hsource : ArrayAt heapLimit source xs entry)
    (hdestination : ArrayAt heapLimit destination ys entry) :
    ∃ finish,
      FunctionExec program heapLimit depth copyFunctions.function.copy
        (copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length))
        entry [] finish ∧
      ArrayAt heapLimit source xs finish ∧ ArrayAt heapLimit destination xs finish ∧
      ArrayFrame destination xs.length entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev := by
  obtain ⟨value, finish, execution, empty, result⟩ :=
    copy_function_contract (program := program) (depth := depth) hw hlen hfit hdisjoint
      (copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length))
      entry ⟨rfl, hsource, hdestination⟩
  subst value
  exact ⟨finish, execution, result⟩

/-- The function body's bound comes from the existing copy loop proof. This
does not include the enclosing call's argument evaluation or return sequence;
their actual generated instruction counts are added at the call site. -/
theorem copy_function_timeBound {w control heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length) (hfit : xs.length < 2 ^ w)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length) :
    FunctionTimeBound control program heapLimit depth copyFunctions.function.copy
      (fun args entry =>
        args = copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length) ∧
        ArrayAt heapLimit source xs entry ∧ ArrayAt heapLimit destination ys entry)
      (fun _ _ => 19 * xs.length + 2) := by
  apply FunctionTimeBound.of_body
    (copy_timeBound (control := control) (program := program) (depth := depth) hw hlen hdisjoint)
  · rintro args entry ⟨rfl, sourceArray, destinationArray⟩
    refine ⟨sourceArray, destinationArray, rfl, rfl, ?_⟩
    exact Word.ofNat_toNat_of_lt hfit
  · intro args entry pre
    exact Nat.le_refl _

/-- Functional correctness and the separate time proof describe one invocation
of the declared function, with its actual body count and mathematical result. -/
theorem copy_function_runs_with_timeBound {w control heapLimit depth : Nat} {program : Program}
    {source destination : Word w} {xs ys : List (Word w)} (hw : 0 < w)
    (hlen : ys.length = xs.length) (hfit : xs.length < 2 ^ w)
    (hdisjoint : ArraysDisjoint source xs.length destination xs.length)
    (entry : State w) (hsource : ArrayAt heapLimit source xs entry)
    (hdestination : ArrayAt heapLimit destination ys entry) :
    ∃ bodySteps finish,
      FunctionMeasuredExec control program heapLimit depth copyFunctions.function.copy
        (copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length))
        bodySteps entry [] finish ∧
      ArrayAt heapLimit source xs finish ∧ ArrayAt heapLimit destination xs finish ∧
      ArrayFrame destination xs.length entry.mem finish.mem ∧
      finish.input = entry.input ∧ finish.outputRev = entry.outputRev ∧
      bodySteps ≤ 19 * xs.length + 2 := by
  obtain ⟨bodySteps, value, finish, execution, ⟨empty, result⟩, bound⟩ :=
    (copy_function_contract (program := program) (depth := depth) hw hlen hfit hdisjoint).with_timeBound
      (copy_function_timeBound (control := control) hw hlen hfit hdisjoint)
      (copyFunctions.arguments.copy source destination (BitVec.ofNat w xs.length))
      entry ⟨rfl, hsource, hdestination⟩
  subst value
  exact ⟨bodySteps, finish, execution, result.1, result.2.1, result.2.2.1,
    result.2.2.2.1, result.2.2.2.2, bound⟩

end Ram.Source.Array
