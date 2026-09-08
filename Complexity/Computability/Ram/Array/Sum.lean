/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Complexity.Computability.Ram.Array.ForIn.Expression
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Function.Time
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Tactic.Ram.Total

/-!
# A callable function summing a represented array

`sumFunctions` provides a named executable function over a typed array reference,
lowered to its existing pointer and length words. Its `sumPair` function calls
the same sum implementation on two references.
`sum_function_contract` states its return value using the ordinary list of
represented words, and proves that every caller state field is unchanged.
No stream I/O or `main` is needed. The implementation performs each load and
word addition through a scoped `for` traversal, preserving the array descriptor;
the mathematical list is a specification of existing memory.

Correctness and termination are independent of a time bound. The separate
`sum_function_timeBound` counts the same body, including initialization and
loop guards. Sum arithmetic wraps modulo the word width; exact natural sums
are recovered under an explicit no-overflow hypothesis.
-/

namespace Ram.Source.Array

/-- Mathematical specification: sum the decoded values, then encode modulo
the machine-word range. This definition is not part of the executed program. -/
def wordSum (xs : List (Word w)) : Word w :=
  BitVec.ofNat w (xs.map BitVec.toNat).sum

/-- The encoded mathematical sum is the ordinary sum of machine words.
The standard list algebra therefore applies without a separate modular fold. -/
theorem wordSum_eq_sum (xs : List (Word w)) : wordSum xs = xs.sum := by
  unfold wordSum
  change BitVec.ofNat w ((xs.map BitVec.toNat).foldr (· + ·) 0) =
    xs.foldr (· + ·) (BitVec.ofNat w 0)
  rw [List.foldr_map]
  exact (List.foldr_hom (BitVec.ofNat w) (l := xs) (init := 0)
    (g₁ := fun x y => x.toNat + y) (g₂ := fun x y => x + y)
    (fun x y => by rw [BitVec.ofNat_add, Word.ofNat_toNat_self])).symm

@[simp] theorem wordSum_nil : wordSum ([] : List (Word w)) = 0 := rfl

@[simp] theorem wordSum_cons (x : Word w) (xs : List (Word w)) :
    wordSum (x :: xs) = x + wordSum xs := by
  simp only [wordSum_eq_sum, List.sum_cons]

/-- Summing a concatenation is ordinary addition of the two modular sums. -/
theorem wordSum_append (xs ys : List (Word w)) :
    wordSum (xs ++ ys) = wordSum xs + wordSum ys := by
  simp only [wordSum_eq_sum, List.sum_append]

theorem wordSum_toNat (xs : List (Word w)) :
    (wordSum xs).toNat = (xs.map BitVec.toNat).sum % 2 ^ w := by
  rw [wordSum, BitVec.toNat_ofNat]

/-- A reusable function over an existing array, with no input/output driver. -/
ram_def sumFunctions := ram_functions% {
  fn sum(xs : array) {
    let mut accumulator := 0;
    for x in xs {
      accumulator += x;
    }
    return accumulator;
  }
  fn sumPair(left : array, right : array) {
    let leftSum ← call sum(left);
    let rightSum ← call sum(right);
    return leftSum + rightSum;
  }
}

/-- The array-sum function returns the modular sum and leaves the entire caller
state unchanged. Preconditions describe only arguments and the mathematical
array view; there is no input/output entry point or instruction budget. -/
theorem sum_function_contract {w heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit depth sumFunctions.function.sum
      (fun args entry =>
        args = sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩ ∧
        ArrayAt heapLimit base xs entry)
      (fun _ entry value finish => value = [wordSum xs] ∧ finish = entry) := by
  have hlength : xs.length < 2 ^ w := by omega
  have correct := ForIn.Expression.function_contract
    (program := program) (heapLimit := heapLimit) (depth := depth) (step := fun a x => a + x)
    sumFunctions.body_eq.sum sumFunctions.result_eq.sum
    (⟨base, BitVec.ofNat w xs.length⟩ : ArrayRef w) [] rfl (by decide) hw
    (fun _ _ => ⟨trivial, trivial⟩) (fun _ _ => rfl) xs hfit
  rw [wordSum_eq_sum, List.sum_eq_foldl]
  simpa only [List.append_nil, ArrayRef.rep_mk_iff hlength,
    sumFunctions.arguments.sum, ArrayRef.args] using correct

/-- Call array sum directly on represented contents. No caller register, input
stream or output buffer is needed, and every caller state field is preserved. -/
theorem sum_function_runs {w heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
      entry [wordSum xs] entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    sum_function_contract (program := program) (depth := depth) hw hfit
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
      entry ⟨rfl, represented⟩
  exact execution

/-- Under a mathematical no-overflow hypothesis, the returned word decodes to
the ordinary natural-number list sum. This describes every actual invocation,
not a result function installed as the program's semantics. -/
theorem sum_function_result {w heapLimit depth : Nat} {program : Program}
    {base value : Word w} {xs : List (Word w)} {entry finish : State w}
    (hw : 0 < w) (hfit : base.toNat + xs.length < 2 ^ w)
    (represented : ArrayAt heapLimit base xs entry)
    (hsum : (xs.map BitVec.toNat).sum < 2 ^ w)
    (execution : FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩) entry [value] finish) :
    value.toNat = (xs.map BitVec.toNat).sum ∧ finish = entry := by
  obtain ⟨result, unchanged⟩ :=
    (sum_function_contract (program := program) (depth := depth) hw hfit).post
      ⟨rfl, represented⟩ execution
  have returned : value = wordSum xs := (List.cons.inj result).1
  exact ⟨by rw [returned, wordSum_toNat, Nat.mod_eq_of_lt hsum], unchanged⟩

/-- The same function body has its compiler-derived linear bound, independently
of the correctness theorem. Enclosing argument evaluation, frame setup and
return instructions are charged by the function call rule, not this body bound. -/
theorem sum_function_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth sumFunctions.function.sum
      (fun args entry =>
        args = sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩ ∧
        ArrayAt heapLimit base xs entry)
      (fun _ _ => 18 * xs.length + 8) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish execution
  have hlength : xs.length < 2 ^ w := by omega
  have exactExecution : FunctionMeasuredExec control program heapLimit depth
      sumFunctions.function.sum
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
      (18 * xs.length + 8) entry value finish :=
    ForIn.Expression.function_measured sumFunctions.body_eq.sum
      (⟨base, BitVec.ofNat w xs.length⟩ : ArrayRef w) [] rfl (by decide) hw xs
      ⟨Word.ofNat_toNat_of_lt hlength, represented⟩ execution.erase
  exact (execution.deterministic exactExecution).1.le

/-- Combining correctness with its separate cost proof yields one invocation
with the same mathematical result, unchanged caller state and actual body count. -/
theorem sum_function_runs_with_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    ∃ bodySteps,
      FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
        (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
        bodySteps entry [wordSum xs] entry ∧ bodySteps ≤ 18 * xs.length + 8 := by
  obtain ⟨bodySteps, value, finish, execution, ⟨rfl, rfl⟩, bound⟩ :=
    (sum_function_contract (program := program) (depth := depth) hw hfit).with_timeBound
      (sum_function_timeBound (control := control) hw hfit)
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
      entry ⟨rfl, represented⟩
  exact ⟨bodySteps, execution, bound⟩

/-- The same sum contract accepts one typed array reference. Its mathematical
contents are the existing list representation, not part of the runtime argument. -/
theorem sum_function_contract_of_ref {w heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract program heapLimit depth sumFunctions.function.sum
      (fun args entry => args = sumFunctions.arguments.sum array ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish => value = [wordSum xs] ∧ finish = entry) := by
  apply (sum_function_contract (program := program) (depth := depth)
    (base := array.base) (xs := xs) hw hfit).consequence
  · rintro args entry ⟨rfl, represented⟩
    refine ⟨?_, represented.2⟩
    simp only [sumFunctions.arguments.sum, represented.length_eq]
  · intro args entry value finish _ result
    exact result

/-- The typed sum interface retains the same conditional body bound, independently
of correctness. The represented length supplies the existing word-level premise. -/
theorem sum_function_timeBound_of_ref {w control heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth sumFunctions.function.sum
      (fun args entry => args = sumFunctions.arguments.sum array ∧
        array.Rep heapLimit xs entry)
      (fun _ _ => 18 * xs.length + 8) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish execution
  apply sum_function_timeBound (control := control) (program := program) (depth := depth)
    (base := array.base) (xs := xs) hw hfit
    (sumFunctions.arguments.sum array) entry ?_ steps value finish execution
  refine ⟨?_, represented.2⟩
  simp only [sumFunctions.arguments.sum, represented.length_eq]

/-- A typed reference supplies the complete runtime array argument to the same
function invocation, while the list appears only in the specification. -/
theorem sum_function_runs_of_ref {w heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : array.Rep heapLimit xs entry) :
    FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum array) entry [wordSum xs] entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    sum_function_contract_of_ref (program := program) (depth := depth) hw hfit
      (sumFunctions.arguments.sum array) entry ⟨rfl, represented⟩
  exact execution

/-- The typed invocation has the existing sum body's exact count, including
initialization and loop guards but excluding its enclosing call overhead. -/
theorem sum_function_measured_of_ref {w control heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : array.Rep heapLimit xs entry) :
    FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum array) (18 * xs.length + 8) entry [wordSum xs] entry := by
  have execution :=
    sum_function_runs_of_ref (program := program) (depth := depth) hw hfit entry represented
  exact ForIn.Expression.function_measured sumFunctions.body_eq.sum
    array [] rfl (by decide) hw xs represented execution

/-- The typed two-array function makes two real calls to the existing sum.
Their contracts provide the returned mathematical values and preserve the
shared state. Read-only arrays may overlap; no disjointness premise is needed. -/
theorem sumPair_function_contract {w heapLimit depth : Nat} {program : Program}
    {left right : ArrayRef w} {xs ys : List (Word w)} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (lookup : program[sumFunctions.functionIndex.sum]? = some sumFunctions.function.sum) :
    FunctionContract program heapLimit (depth + 1) sumFunctions.function.sumPair
      (fun args entry => args = sumFunctions.arguments.sumPair left right ∧
        left.Rep heapLimit xs entry ∧ right.Rep heapLimit ys entry)
      (fun _ entry value finish => value = [wordSum xs + wordSum ys] ∧ finish = entry) := by
  ram_total_vc args entry ⟨rfl, leftArray, rightArray⟩
    [sumFunctions.body_eq.sumPair, sumFunctions.result_eq.sumPair]
  ram_total_apply (sum_function_contract_of_ref (program := program) (depth := depth)
    (array := left) (xs := xs) hw leftFit) [lookup, leftArray]
  ram_total_apply (sum_function_contract_of_ref (program := program) (depth := depth)
    (array := right) (xs := ys) hw rightFit) [lookup, rightArray]

/-- Invoke the typed pair function on any two represented arrays, using its
actual declaration table and preserving the full caller state. -/
theorem sumPair_function_runs {w heapLimit depth : Nat}
    {left right : ArrayRef w} {xs ys : List (Word w)} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (entry : State w) (leftArray : left.Rep heapLimit xs entry)
    (rightArray : right.Rep heapLimit ys entry) :
    FunctionExec sumFunctions.program heapLimit (depth + 1) sumFunctions.function.sumPair
      (sumFunctions.arguments.sumPair left right) entry [wordSum xs + wordSum ys] entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    sumPair_function_contract (depth := depth) hw leftFit rightFit sumFunctions.function_lookup.sum
      (sumFunctions.arguments.sumPair left right) entry ⟨rfl, leftArray, rightArray⟩
  exact execution

private theorem sum_call_steps (control pointer length bodySteps : Nat) :
    (ABI.callPrefixLocals control sumFunctions.function.sum.locals
      [.var pointer, .var length] 0).length + 1 + bodySteps +
        (ABI.returnCodeResultsLocals control sumFunctions.function.sum.locals
          sumFunctions.function.sum.results).length + 1 = bodySteps + 58 := by
  rw [ABI.callPrefixLocals_length_eq, ABI.returnCodeResultsLocals_length]
  change 2 + 2 + 4 * 6 + 4 + 1 + bodySteps + (1 + 1 + 3 * 6 + 4) + 1 = bodySteps + 58
  omega

/-- Exact execution of the pair body: both inner calls include their actual
argument evaluation, frame setup, returns and linking transitions. The outer
pair call's own setup and return are not included in this body count. -/
theorem sumPair_function_measured {w control heapLimit depth : Nat} {program : Program}
    {left right : ArrayRef w} {xs ys : List (Word w)} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (lookup : program[sumFunctions.functionIndex.sum]? = some sumFunctions.function.sum)
    (entry : State w) (leftArray : left.Rep heapLimit xs entry)
    (rightArray : right.Rep heapLimit ys entry) :
    FunctionMeasuredExec control program heapLimit (depth + 1) sumFunctions.function.sumPair
      (sumFunctions.arguments.sumPair left right) (18 * (xs.length + ys.length) + 132)
      entry [wordSum xs + wordSum ys] entry := by
  let entered := entry.enter (sumFunctions.arguments.sumPair left right)
  let middle := entered.setReg sumFunctions.localReg.sumPair.leftSum (wordSum xs)
  have first : FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
      ([.var sumFunctions.localReg.sumPair.left.base,
        .var sumFunctions.localReg.sumPair.left.length].map entered.eval)
      (18 * xs.length + 8) entered [wordSum xs] entered :=
    sum_function_measured_of_ref hw leftFit entered (leftArray.enter _)
  have firstCall := first.call (dsts := [sumFunctions.localReg.sumPair.leftSum]) lookup
    rfl (by simp [Expr.ReadsBelow])
  simp only [List.length_singleton, State.setRegs_singleton] at firstCall
  rw [sum_call_steps] at firstCall
  have second : FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
      ([.var sumFunctions.localReg.sumPair.right.base,
        .var sumFunctions.localReg.sumPair.right.length].map middle.eval)
      (18 * ys.length + 8) middle [wordSum ys] middle :=
    sum_function_measured_of_ref hw rightFit middle
      ((rightArray.enter _).setReg sumFunctions.localReg.sumPair.leftSum (wordSum xs))
  have secondCall := second.call (dsts := [sumFunctions.localReg.sumPair.rightSum]) lookup
    rfl (by simp [Expr.ReadsBelow])
  simp only [List.length_singleton, State.setRegs_singleton] at secondCall
  rw [sum_call_steps] at secondCall
  have body : LocalMeasuredExec control program heapLimit (depth + 1)
      sumFunctions.function.sumPair.body (18 * (xs.length + ys.length) + 132)
      entered (middle.setReg sumFunctions.localReg.sumPair.rightSum (wordSum ys)) := by
    rw [sumFunctions.body_eq.sumPair]
    have counts : (18 * xs.length + 8 + 58) + (18 * ys.length + 8 + 58) =
        18 * (xs.length + ys.length) + 132 := by omega
    rw [← counts]
    exact firstCall.seq secondCall
  exact FunctionMeasuredExec.of_body
    (sumFunctions.arguments_length.sumPair left right) (by decide) body
    (by simp [sumFunctions.result_eq.sumPair, Expr.ReadsBelow])

/-- The semantic body-time observation has the count proved from the same two
real calls. The outer call and any executable adapter are outside its scope. -/
theorem sumPair_bodyTime_eq {w heapLimit : Nat} {program : Program}
    {left right : ArrayRef w} {xs ys : List (Word w)} (hw : 0 < w)
    (leftFit : left.base.toNat + xs.length < 2 ^ w)
    (rightFit : right.base.toNat + ys.length < 2 ^ w)
    (lookup : program[sumFunctions.functionIndex.sum]? = some sumFunctions.function.sum)
    (entry : State w) (leftArray : left.Rep heapLimit xs entry)
    (rightArray : right.Rep heapLimit ys entry) :
    sumFunctions.function.sumPair.bodyTime program heapLimit
      (sumFunctions.arguments.sumPair left right) entry =
        Part.some (18 * (xs.length + ys.length) + 132) :=
  (sumPair_function_measured (control := 0) (depth := 0) hw leftFit rightFit lookup
    entry leftArray rightArray).bodyTime_eq_some

end Ram.Source.Array
