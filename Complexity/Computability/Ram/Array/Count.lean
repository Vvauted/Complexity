/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn.Expression
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Named.Declaration
import Mathlib.Data.List.Count

/-!
# Counting occurrences in a represented array

`countFunctions` declares one executable function over an array reference and
a target word. The mathematical result is Lean's `List.count`, not a second
counting implementation. The source-derived expression rule handles traversal,
termination, framing and preservation of the captured target parameter. Its
mathematical step is an ordinary word update, proved against the actual expression.

The array is already represented in shared memory. This function performs each
load and equality comparison and returns a word without stream input/output.
The address-range hypothesis also makes its occurrence count exact: it cannot
exceed the represented length. Correctness does not require a time budget.
-/

namespace Ram.Source.Array

/-- Count equal words in an existing array, with a fixed program independent
of the array contents and length. -/
ram_def countFunctions := ram_functions% {
  fn count(xs : array, target) {
    let mut accumulator := 0;
    for x in xs {
      accumulator += (x == target);
    }
    return accumulator;
  }
}

namespace Count

/-- Mathematical update for one visited word. The executable expression below
must refine this update; it is not an uncharged host-language callback. -/
def step (target accumulator value : Word w) : Word w :=
  accumulator + if value = target then 1 else 0

/-- An ordinary list-fold identity, using the standard occurrence count. -/
theorem foldl_step (target accumulator : Word w) (xs : List (Word w)) :
    xs.foldl (step target) accumulator = accumulator + BitVec.ofNat w (xs.count target) := by
  induction xs generalizing accumulator with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      by_cases h : x = target
      · subst x
        simp only [step, ite_true, List.count_cons_self, BitVec.ofNat_add]
        rw [BitVec.add_assoc, BitVec.add_comm (1 : Word w)]
        simp only [BitVec.ofNat_eq_ofNat]
      · simp [step, List.count_cons_of_ne h, h]

end Count

/-- Count occurrences and preserve the caller state. The contract requires no
instruction budget and binds the pointer, length and target automatically. -/
theorem count_function_contract {w heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit depth countFunctions.function.count
      (fun args entry =>
        args = countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target ∧
        ArrayAt heapLimit base xs entry)
      (fun _ entry value finish => value = BitVec.ofNat w (xs.count target) ∧ finish = entry) := by
  have correct := ForIn.Expression.function_contract
    (program := program) (heapLimit := heapLimit) (depth := depth)
    (step := Count.step target) countFunctions.body_eq.count countFunctions.result_eq.count
    ⟨base, BitVec.ofNat w xs.length⟩ [target] rfl (by decide) hw
    (by intros; simp [Expr.ReadsBelow])
    (by
      intro current parameters
      have captured := parameters countFunctions.localReg.count.target (by decide)
      dsimp [ArrayRef.args, countFunctions.localReg.count.target] at captured
      simp [State.eval, Expr.eval, BinOp.eval, Count.step, captured]) xs hfit
  apply correct.consequence
  · rintro args entry ⟨rfl, represented⟩
    exact ⟨rfl, Word.ofNat_toNat_of_lt (by omega), represented⟩
  · intro args entry value finish _ post
    simpa [Count.foldl_step] using post

/-- An invocation of the actual function, with no main program or I/O adapter. -/
theorem count_function_runs {w heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    FunctionExec program heapLimit depth countFunctions.function.count
      (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)
      entry (BitVec.ofNat w (xs.count target)) entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    count_function_contract (program := program) (depth := depth) hw hfit
      (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)
      entry ⟨rfl, represented⟩
  exact execution

/-- The decoded function value is the standard natural-number count. The
length bound already rules out result overflow, since a count is at most the
number of represented words. -/
theorem count_function_eval_toNat {w heapLimit : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} {entry : State w} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (represented : ArrayAt heapLimit base xs entry) :
    (countFunctions.function.count.eval program heapLimit
      (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target) entry).map
        (fun result => result.1.toNat) = Part.some (xs.count target) := by
  rw [(count_function_runs (program := program) (depth := 0)
    hw hfit entry represented).eval_eq_some]
  have exactCount : xs.count target < 2 ^ w :=
    lt_of_le_of_lt List.count_le_length (by omega)
  simp [Word.ofNat_toNat_of_lt exactCount]

/-- A separate bound on this function's actual compiled body count. It does
not include an enclosing caller's argument evaluation, frame or return code.
The count includes the copied descriptor, element bindings and real comparisons. -/
theorem count_function_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth countFunctions.function.count
      (fun args entry =>
        args = countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target ∧
        ArrayAt heapLimit base xs entry)
      (fun _ _ => 20 * xs.length + 8) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish execution
  have hlength : xs.length < 2 ^ w := by omega
  have measured := ForIn.Expression.function_measured (control := control)
    countFunctions.body_eq.count ⟨base, BitVec.ofNat w xs.length⟩ [target]
    rfl (by decide) hw xs ⟨Word.ofNat_toNat_of_lt hlength, represented⟩ execution.erase
  have same := (execution.deterministic measured).1
  change steps = 20 * xs.length + 8 at same
  exact Nat.le_of_eq same

/-- Correctness and cost describe a single invocation of the declared function. -/
theorem count_function_runs_with_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    ∃ bodySteps,
      FunctionMeasuredExec control program heapLimit depth countFunctions.function.count
        (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)
        bodySteps entry (BitVec.ofNat w (xs.count target)) entry ∧
      bodySteps ≤ 20 * xs.length + 8 := by
  obtain ⟨bodySteps, value, finish, execution, ⟨rfl, rfl⟩, bound⟩ :=
    (count_function_contract (program := program) (depth := depth) hw hfit).with_timeBound
      (count_function_timeBound (control := control) hw hfit)
      (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)
      entry ⟨rfl, represented⟩
  exact ⟨bodySteps, execution, bound⟩

/-- Pass one typed array reference and one scalar target to the same count
function. The reference assertion supplies the exact represented length. -/
theorem count_function_contract_of_ref {w heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit depth countFunctions.function.count
      (fun args entry => args = countFunctions.arguments.count array target ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish => value = BitVec.ofNat w (xs.count target) ∧ finish = entry) := by
  apply (count_function_contract (program := program) (depth := depth)
    (base := array.base) (target := target) (xs := xs) hw hfit).consequence
  · rintro args entry ⟨rfl, represented⟩
    refine ⟨?_, represented.2⟩
    simp only [countFunctions.arguments.count, represented.length_eq]
  · intro args entry value finish _ result
    exact result

/-- The actual count invocation has this exact body count, including the
descriptor copies, element loads, comparisons and loop control. Enclosing call
instructions are added by the ordinary function-call rule. -/
theorem count_function_measured_of_ref {w control heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : array.Rep heapLimit xs entry) :
    FunctionMeasuredExec control program heapLimit depth countFunctions.function.count
      (countFunctions.arguments.count array target) (20 * xs.length + 8)
      entry (BitVec.ofNat w (xs.count target)) entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    count_function_contract_of_ref (program := program) (depth := depth) hw hfit
      (countFunctions.arguments.count array target) entry ⟨rfl, represented⟩
  exact ForIn.Expression.function_measured (control := control) countFunctions.body_eq.count
    array [target] rfl (by decide) hw xs represented execution

/-- Observe a standard list count through a typed reference, without exposing
the descriptor's two-word argument encoding to the caller's proof. -/
theorem count_function_eval_toNat_of_ref {w heapLimit : Nat} {program : Program}
    {array : ArrayRef w} {target : Word w} {xs : List (Word w)} {entry : State w}
    (hw : 0 < w) (hfit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    (countFunctions.function.count.eval program heapLimit
      (countFunctions.arguments.count array target) entry).map
        (fun result => result.1.toNat) = Part.some (xs.count target) := by
  simpa only [countFunctions.arguments.count, represented.length_eq] using
    (count_function_eval_toNat (program := program) (target := target) hw hfit represented.2)

/-- Typed argument packaging preserves the same compiler-derived body bound;
it neither allocates a descriptor nor adds a representation-conversion step. -/
theorem count_function_timeBound_of_ref {w control heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth countFunctions.function.count
      (fun args entry => args = countFunctions.arguments.count array target ∧
        array.Rep heapLimit xs entry)
      (fun _ _ => 20 * xs.length + 8) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish execution
  apply count_function_timeBound (control := control) (program := program) (depth := depth)
    (base := array.base) (target := target) (xs := xs) hw hfit
    (countFunctions.arguments.count array target) entry ?_ steps value finish execution
  refine ⟨?_, represented.2⟩
  simp only [countFunctions.arguments.count, represented.length_eq]

end Ram.Source.Array
