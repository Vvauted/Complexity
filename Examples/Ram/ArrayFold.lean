/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Complexity.Computability.Ram.Array.ForIn.Function
import Complexity.Computability.Ram.Source.Function.Linking
import Complexity.Computability.Ram.Compiler.Local.Function.Typed
import Complexity.Tactic.Ram.Run
import Complexity.Tactic.Ram.Time
import Examples.Ram.Factorial
import Examples.Ram.LocalBindings

/-!
# Folding an array through a proved function

The `sumSquares` function in `LocalBindings.functions` calls `addSquare` for
each represented word. That step calls the existing `square` function; neither
the traversal proof nor the mathematical specification supplies a second
squaring implementation. The specification is the ordinary natural-number sum
of the squared decoded words, encoded back into the word range.

The source uses a scoped `for` element binding. Generated body and return
equations select the shared function rule, so this proof does not name the
private cursor, extract call expressions or reconstruct parameter frames.
-/

namespace Ram.Examples.ArrayFold

open LocalBindings
open Source Source.Array

/-- The word-valued fold is the encoded ordinary sum of natural squares.
This equation uses list homomorphisms, independently of a machine execution. -/
theorem foldl_addSquare (xs : List (Word w)) :
    xs.foldl (fun accumulator x => accumulator + x * x) 0 =
      BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum := by
  have squares : (xs.map (fun x => x.toNat ^ 2)).map (BitVec.ofNat w) =
      xs.map (fun x => x * x) := by
    simp [List.map_map, pow_two, BitVec.ofNat_mul]
  have mapped := List.foldl_map_hom
    (g := BitVec.ofNat w) (f := Nat.add) (f' := fun a b => a + b)
    (a := 0) (l := xs.map (fun x => x.toNat ^ 2))
    (fun a b => (BitVec.ofNat_add a b).symm)
  rw [squares, List.foldl_map] at mapped
  simpa only [List.sum_eq_foldl] using mapped

/-- The function returns the mathematical sum of squares through its word
encoding and preserves caller state. No stream driver or time bound is needed. -/
theorem function_contract {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w) :
    FunctionContract functions.program heapLimit 2 functions.function.sumSquares
      (fun args entry => args = functions.arguments.sumSquares array ∧
        array.Rep heapLimit xs entry)
      (fun _ entry value finish =>
        value = [BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum] ∧ finish = entry) := by
  have correct := ForIn.function_contract functions.body_eq.sumSquares
    functions.result_eq.sumSquares rfl (by decide) hw functions.function_lookup.addSquare
    (addSquare_contract heapLimit) array xs fit
  exact correct.consequence (fun _ _ pre => pre)
    (fun _ _ _ _ _ post =>
      ⟨post.1.trans (congrArg (fun value => [value]) (foldl_addSquare xs)), post.2⟩)

/-- Observe the same implemented function using an ordinary list expression. -/
theorem eval_eq {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    functions.eval.sumSquares array heapLimit entry =
      Part.some (BitVec.ofNat w (xs.map (fun x => x.toNat ^ 2)).sum, entry) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    function_contract hw fit (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  exact execution.evalTyped_eq_some functions.results_length.sumSquares

/-- When the mathematical sum fits, the decoded result is exactly that natural
number. The modular theorem above does not assume intermediate no-overflow. -/
theorem eval_toNat {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry)
    (resultFit : (xs.map (fun x => x.toNat ^ 2)).sum < 2 ^ w) :
    (functions.eval.sumSquares array heapLimit entry).map (fun result => result.1.toNat) =
      Part.some (xs.map (fun x => x.toNat ^ 2)).sum := by
  rw [eval_eq hw fit represented]
  simp only [Part.map_some, Word.ofNat_toNat_of_lt resultFit]

/-- Body time is observed from the terminating implementation and then
identified by the independent loop count. It includes both nested calls. -/
theorem bodyTime_eq {heapLimit : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (represented : array.Rep heapLimit xs entry) :
    functions.bodyTime.sumSquares array heapLimit entry = Part.some (76 * xs.length + 8) := by
  obtain ⟨value, finish, execution, _⟩ :=
    function_contract hw fit (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  have time := ForIn.function_bodyTime (control := functions.registers)
    functions.body_eq.sumSquares (by decide) hw functions.function_lookup.addSquare
    addSquare_body_steps array xs represented execution
  change functions.bodyTime.sumSquares array heapLimit entry =
    Part.some (76 * xs.length + 8) at time
  exact time

/-- Execute the same declared fold on a preloaded array. The projection retains
the returned word, full call count and stopping reason; it performs no list loading. -/
def runSumSquares (array : ArrayRef 32) (heapLimit : Nat) (entry : Source.State 32) :
    Option (Nat × Nat × StopReason) :=
  (functions.run.sumSquares array heapLimit entry).map fun result =>
    ((result.state.regs 0).toNat, result.steps, result.reason)

/-- The executable function application returns that list sum and the complete
machine count, including its enclosing call and halt. Memory is preloaded;
stack capacity is a safety premise, not a proposed execution budget. -/
theorem runSumSquares_eq {heapLimit : Nat} {array : ArrayRef 32}
    {xs : List (Word 32)} {entry : Source.State 32}
    (fit : array.base.toNat + xs.length < 2 ^ 32)
    (hstack : heapLimit + 3 * ABI.frameSize functions.registers < 2 ^ 32)
    (represented : array.Rep heapLimit xs entry) :
    runSumSquares array heapLimit entry =
      some ((xs.map (fun x => x.toNat ^ 2)).sum % 2 ^ 32, 76 * xs.length + 67, .halted) := by
  let code := LocalCompiler.rawLink functions.registers functions.program
    (LocalCompiler.Function.trampoline functions.functionIndex.sumSquares
      functions.function.sumSquares.params functions.function.sumSquares.results.length)
  have hcompile : LocalCompiler.Function.compile functions.registers functions.program
      functions.functionIndex.sumSquares functions.function.sumSquares.params = some code := by
    set_option maxRecDepth 4096 in decide
  have hcode : code.length < 2 ^ 32 := by
    set_option maxRecDepth 4096 in decide
  obtain ⟨value, finish, execution, rfl, rfl⟩ := function_contract (by decide : 0 < 32) fit
    (functions.arguments.sumSquares array) entry ⟨rfl, represented⟩
  obtain ⟨target, returned, value, _⟩ :=
    LocalCompiler.Function.runUntil_eq_of_execution hcompile
      functions.function_lookup.sumSquares hcode hstack execution
      (bodyTime_eq (by decide : 0 < 32) fit represented)
  change [target.regs 0] = [BitVec.ofNat 32 (xs.map (fun x => x.toNat ^ 2)).sum] at value
  have scalarValue := (List.cons.inj value).1
  have count : LocalCompiler.Function.callSteps functions.registers
      functions.function.sumSquares (76 * xs.length + 8) + 1 = 76 * xs.length + 67 := by
    simp [LocalCompiler.Function.callSteps_eq, Nat.add_assoc]
    decide
  simp only [runSumSquares, functions.run.sumSquares,
    max_eq_right (by decide : 1 ≤ functions.registers), returned, Option.map_some, scalarValue,
    BitVec.toNat_ofNat, count]

-- The three preloaded words are 1, 2, 3. Every visited word triggers both
-- addSquare and the existing square function; these are real compiled calls.
#eval runSumSquares ⟨0, 3⟩ 3
  { Source.State.initial [] with mem := fun address => BitVec.ofNat 32 (address.toNat + 1) }

namespace Factorials

/-- A varying-cost fold imports the existing recursive factorial implementation.
The adapter performs one actual call; the traversal performs one adapter call
per represented array element. Neither source body computes a host-side list. -/
ram_def functions := ram_functions% {
  include Factorial.functions as Factorial;
  fn addFactorial(accumulator, x) {
    let factorialValue ← call Factorial.factorial(x);
    return accumulator + factorialValue;
  }
  fn sumFactorials(xs : array) {
    let mut accumulator := 0;
    for x in xs {
      accumulator := call addFactorial(accumulator, x);
    }
    return accumulator;
  }
}

/-- The mathematical update describes the adapter's returned word, including
the word model's modular factorial and addition. It is not executable source. -/
def step (accumulator x : Word w) : Word w :=
  accumulator + Factorial.value w x.toNat

/-- A bound on this element gives sufficient recursive call depth. Correctness
uses only the imported factorial contract, without a proposed instruction budget. -/
theorem addFactorial_contract (heapLimit K : Nat) (accumulator x : Word w)
    (bounded : x.toNat ≤ K) :
    FunctionContract functions.program heapLimit (K + 1) functions.function.addFactorial
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry) := by
  have factorialContract := (Factorial.function_contract heapLimit x.toNat x.isLt).renameCalls
    functions.embeds.Factorial
  simp only [Word.ofNat_toNat_self] at factorialContract
  ram_total_vc args entry rfl
    [functions.body_eq.addFactorial, functions.result_eq.addFactorial, step]
  ram_total_apply factorialContract [functions.function_lookup.Factorial.factorial]

/-- Transfer the independent factorial bound to the imported implementation at
any completed invocation's depth. A real invocation at the original sufficient
depth supplies the comparison; a conditional bound alone is not monotone in depth. -/
private theorem factorial_timeBound (control heapLimit depth : Nat) (x : Word w) :
    FunctionTimeBound control functions.program heapLimit depth
      functions.function.Factorial.factorial
      (fun args _ => args = [x]) (fun _ _ => 37 * x.toNat + 4) := by
  rintro args entry rfl steps value finish invocation
  have original := Factorial.function_runs heapLimit x.toNat x.isLt entry
  obtain ⟨originalSteps, measured⟩ := original.exists_measured 2
  have bounded := Factorial.function_timeBound heapLimit x.toNat x.isLt
    _ entry rfl _ _ _ measured
  have imported := measured.renameCalls functions.embeds.Factorial
  simp only [Word.ofNat_toNat_self] at imported
  rw [(invocation.deterministic imported).1]
  exact bounded

/-- The adapter body pays the factorial body's input-dependent bound and its
actual 28-step call overhead. Its final addition belongs to its own return code. -/
theorem addFactorial_timeBound (control heapLimit depth : Nat) (accumulator x : Word w) :
    FunctionTimeBound control functions.program heapLimit (depth + 1)
      functions.function.addFactorial
      (fun args _ => args = [accumulator, x]) (fun _ _ => 37 * x.toNat + 32) := by
  ram_time_vc args entry rfl [functions.body_eq.addFactorial]
  ram_time_call (factorial_timeBound control heapLimit depth x)
    [functions.function_lookup.Factorial.factorial, Factorial.functions.result_eq.factorial]

/-- The machine-word fold is the encoding of the ordinary sum of factorials.
No no-overflow claim is implicit in this equality. -/
theorem foldl_step (xs : List (Word w)) :
    xs.foldl step 0 = BitVec.ofNat w (xs.map (fun x => Nat.factorial x.toNat)).sum := by
  have mapped := List.foldl_map_hom
    (g := BitVec.ofNat w) (f := Nat.add) (f' := fun a b => a + b)
    (a := 0) (l := xs.map (fun x => Nat.factorial x.toNat))
    (fun a b => (BitVec.ofNat_add a b).symm)
  simpa only [List.foldl_map, List.sum_eq_foldl, step, Factorial.value,
    Factorial.factorialNat] using mapped

/-- Sum the actual element-dependent factorial-call bounds. The additional
53 steps per element pay the adapter's enclosing call and the traversal;
the final eight steps initialize and finish the array function's body. -/
def bodyBudget (xs : List (Word w)) : Nat :=
  (xs.map (fun x => 37 * x.toNat + 32)).sum + 53 * xs.length + 8

/-- The returned scalar is an ordinary mathematical fold. The array is already
represented in the entry heap, and the element bound supplies recursive depth;
the invocation preserves every part of the caller's shared state. -/
theorem typed_contract {heapLimit K : Nat} {xs : List (Word w)}
    (hw : 0 < w) (bounded : ∀ x ∈ xs, x.toNat ≤ K) :
    TypedFunctionContract functions.program heapLimit (K + 2)
      functions.function.sumFactorials .word functions.arguments.sumFactorials
      (fun array entry => array.Rep heapLimit xs entry ∧
        array.base.toNat + xs.length < 2 ^ w)
      (fun _ entry value finish => value = xs.foldl step 0 ∧ finish = entry) := by
  rintro array entry ⟨represented, fit⟩
  have correct := ForIn.function_contract_of_step
    (I := fun _ => True) (Allowed := fun x : Word w => x.toNat ≤ K)
    (bodyShape := functions.body_eq.sumFactorials)
    (resultShape := functions.result_eq.sumFactorials) (params := rfl)
    (layout := by decide) (hw := hw) (lookup := functions.function_lookup.addFactorial)
    (correct := fun a x _ hx => addFactorial_contract heapLimit K a x hx)
    (preserve := fun _ _ _ _ => trivial) (array := array) (xs := xs)
    (initial := trivial) (admissible := bounded) (fit := fit)
  obtain ⟨value, finish, execution, rfl, rfl⟩ := correct array.args entry ⟨rfl, represented⟩
  exact ⟨_, _, execution, rfl, rfl⟩

/-- The declaration's typed semantic result describes the implemented fold,
not a second factorial algorithm or a stream-output wrapper. -/
theorem eval_eq {heapLimit K : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) (represented : array.Rep heapLimit xs entry) :
    functions.eval.sumFactorials array heapLimit entry = Part.some (xs.foldl step 0, entry) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    typed_contract hw bounded array entry ⟨represented, fit⟩
  exact execution.evalTyped_eq_some functions.results_length.sumFactorials

/-- With no overflow in the mathematical sum, the implemented fold has that
exact natural-number value. Modular semantics remain available without this premise. -/
theorem eval_toNat {heapLimit K : Nat} {array : ArrayRef w} {xs : List (Word w)}
    {entry : Source.State w} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) (represented : array.Rep heapLimit xs entry)
    (resultFit : (xs.map (fun x => Nat.factorial x.toNat)).sum < 2 ^ w) :
    (functions.eval.sumFactorials array heapLimit entry).map (fun result => result.1.toNat) =
      Part.some (xs.map (fun x => Nat.factorial x.toNat)).sum := by
  rw [eval_eq hw fit bounded represented, foldl_step]
  simp only [Part.map_some, Word.ofNat_toNat_of_lt resultFit]

private theorem addFactorial_overhead (control accumulator element : Nat) :
    Fold.Call.callSteps control functions.function.addFactorial
      [.var accumulator, .var element] 0 + 14 = 53 := by
  rw [Fold.Call.callSteps_eq]
  ram_bound [functions.result_eq.addFactorial]

/-- The independent bound sums factorial work at the actual array elements.
Only their admissibility and the accumulator's mathematical invariant are used
to instantiate the general data-dependent traversal rule. -/
theorem function_timeBound {control heapLimit K : Nat} {array : ArrayRef w}
    {xs : List (Word w)} (hw : 0 < w) (fit : array.base.toNat + xs.length < 2 ^ w)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) :
    FunctionTimeBound control functions.program heapLimit (K + 2)
      functions.function.sumFactorials
      (fun args entry => args = functions.arguments.sumFactorials array ∧
        array.Rep heapLimit xs entry) (fun _ _ => bodyBudget xs) := by
  have time := ForIn.function_timeBound_of_step
    (I := fun _ => True) (Allowed := fun x : Word w => x.toNat ≤ K)
    (C := fun _ x => 37 * x.toNat + 32)
    (bodyShape := functions.body_eq.sumFactorials) (layout := by decide)
    (hw := hw) (lookup := functions.function_lookup.addFactorial)
    (correct := fun a x _ hx => addFactorial_contract heapLimit K a x hx)
    (time := fun a x _ _ => addFactorial_timeBound control heapLimit K a x)
    (preserve := fun _ _ _ _ => trivial) (array := array) (xs := xs)
    (initial := trivial) (admissible := bounded) (fit := fit)
  have costs : xs.mapIdx (fun _ x => 37 * x.toNat + 32) =
      xs.map (fun x => 37 * x.toNat + 32) := by
    rw [List.mapIdx_eq_zipIdx_map]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun x : Word w => 37 * x.toNat + 32)) (List.zipIdx_map_fst 0 xs)
  simpa only [bodyBudget, costs, addFactorial_overhead, Nat.add_assoc] using time

/-- Budget-free correctness establishes normal termination of the compiled
invocation. The bound reserves the outer fold frame, adapter frame and recursive
factorial frames; it is a sufficient address-space condition, not a peak-space claim. -/
theorem halts {heapLimit K : Nat} {array : ArrayRef 32} {xs : List (Word 32)}
    {entry : Source.State 32} (fit : array.base.toNat + xs.length < 2 ^ 32)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + (K + 3) * ABI.frameSize functions.registers < 2 ^ 32) :
    LocalCompiler.Function.Halts functions.registers functions.program
      functions.functionIndex.sumFactorials functions.function.sumFactorials.params heapLimit
      (functions.arguments.sumFactorials array) entry := by
  ram_run_apply (LocalCompiler.Function.halts_of_typedContract
    (contract := typed_contract (by decide : 0 < 32) bounded) (pre := ⟨represented, fit⟩))
    [functions.function_lookup.sumFactorials]
  exact hstack

/-- The ordinary executable typed projection returns the mathematical fold
and the unchanged shared state of this same compiled invocation. -/
theorem applyState_eq {heapLimit K : Nat} {array : ArrayRef 32} {xs : List (Word 32)}
    {entry : Source.State 32} (fit : array.base.toNat + xs.length < 2 ^ 32)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + (K + 3) * ABI.frameSize functions.registers < 2 ^ 32) :
    functions.applyState.sumFactorials array heapLimit entry (halts fit bounded represented hstack) =
      (xs.foldl step 0, entry) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    typed_contract (by decide : 0 < 32) bounded array entry ⟨represented, fit⟩
  have returned := by
    ram_run_apply (LocalCompiler.Function.applyStateTyped_eq_of_execution
      (shape := functions.results_length.sumFactorials)
      (h := halts fit bounded represented hstack) (execution := execution))
      [functions.function_lookup.sumFactorials]
    exact hstack
  simpa only [functions.applyState.sumFactorials,
    max_eq_right (by decide : 1 ≤ functions.registers)] using returned

/-- The same executable run pays the element-dependent body bound plus its
actual outer call, return and halt. No array-loading work is included. -/
theorem runTotal_steps_le {heapLimit K : Nat} {array : ArrayRef 32} {xs : List (Word 32)}
    {entry : Source.State 32} (fit : array.base.toNat + xs.length < 2 ^ 32)
    (bounded : ∀ x ∈ xs, x.toNat ≤ K) (represented : array.Rep heapLimit xs entry)
    (hstack : heapLimit + (K + 3) * ABI.frameSize functions.registers < 2 ^ 32) :
    (functions.runTotal.sumFactorials array heapLimit entry
      (halts fit bounded represented hstack)).steps ≤ bodyBudget xs + 59 := by
  obtain ⟨value, finish, execution, _⟩ :=
    typed_contract (by decide : 0 < 32) bounded array entry ⟨represented, fit⟩
  change (LocalCompiler.Function.runTotal functions.registers functions.program
    functions.functionIndex.sumFactorials functions.function.sumFactorials.params heapLimit
    (functions.arguments.sumFactorials array) entry (halts fit bounded represented hstack)).steps ≤ _
  ram_run_bound (LocalCompiler.Function.runTotal_steps_le_of_timeBound
    (h := halts fit bounded represented hstack) (execution := execution)
    (time := function_timeBound (by decide : 0 < 32) fit bounded)
    (pre := ⟨rfl, represented⟩))
    [functions.function_lookup.sumFactorials, functions.result_eq.sumFactorials]
  exact hstack

end Factorials

end Ram.Examples.ArrayFold
