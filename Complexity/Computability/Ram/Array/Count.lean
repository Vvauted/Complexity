/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Fold
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Source.Function.Eval
import Complexity.Computability.Ram.Source.Named.Declaration
import Mathlib.Data.List.Count

/-!
# Counting occurrences in a represented array

`countFunctions` declares one executable function over an array reference and
a target word. The mathematical result is Lean's `List.count`, not a second
counting implementation. The reusable array-fold rule handles traversal,
termination and framing; the function-specific invariant only remembers the
unchanged target parameter.

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
    while xs.length {
      accumulator += (load[xs.base] == target);
      xs.base += 1;
      xs.length -= 1;
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

/-- The source expression selected from the sole executable declaration. -/
def value : Expr :=
  match countFunctions.function.count.body with
  | .seq _ (.while _ (.seq (.assign _ expression) _)) => expression
  | _ => .const 0

/-- The named locals used by the generic traversal. Pairwise separation is a
fact about this declaration, rather than a premise for each caller. -/
def registers : Fold.Registers :=
  ⟨countFunctions.localReg.count.xs.base, countFunctions.localReg.count.xs.length,
    countFunctions.localReg.count.accumulator, by decide, by decide, by decide⟩

/-- The generic fold loop is the body already present in the named function,
not a second independently maintained executable definition. -/
theorem body_eq :
    countFunctions.function.count.body =
      .seq (.assign registers.accumulator (.const 0)) (Fold.loop registers value) := rfl

private theorem value_reads {w heapLimit : Nat} (s : State w)
    (address : (s.regs registers.pointer).toNat < heapLimit) :
    value.ReadsBelow heapLimit s.regs s.mem := by
  exact ⟨trivial, ⟨⟨trivial, address⟩, trivial⟩⟩

private theorem value_eval (target : Word w) (s : State w)
    (same : s.regs countFunctions.localReg.count.target = target) :
    s.eval value = step target (s.regs registers.accumulator)
      (s.mem (s.regs registers.pointer)) := by
  simp [value, countFunctions.body_eq.count, registers, State.eval, Expr.eval, BinOp.eval,
    step, same]

private theorem target_preserved (s : State w) :
    (Fold.stepState registers value s).regs countFunctions.localReg.count.target =
      s.regs countFunctions.localReg.count.target :=
  Fold.stepState_other registers value s (r := countFunctions.localReg.count.target)
    (by decide) (by decide) (by decide)

/-- The generic fold supplies all cursor, termination and framing reasoning.
The only function-specific persistent fact is the unchanged target parameter. -/
theorem body_safe {program : Program} {heapLimit depth : Nat} (hw : 0 < w)
    (s : State w) (base target : Word w) (xs : List (Word w))
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (parameter : s.regs countFunctions.localReg.count.target = target)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit depth countFunctions.function.count.body s t ∧
      t.regs registers.accumulator = BitVec.ofNat w (xs.count target) ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev := by
  let initialized := s.setReg registers.accumulator 0
  obtain ⟨t, execution, result, _, _, _, memory, input, output, _⟩ :=
    Fold.loop_safe registers (value := value) (program := program) (depth := depth)
      (step := step target) (R := fun current =>
        current.regs countFunctions.localReg.count.target = target) hw
      (fun current _ address => value_reads current address)
      (value_eval target)
      (fun current same => (target_preserved current).trans same)
      initialized base xs (by exact parameter) represented (by exact pointer)
      (by exact count) heap fit
  refine ⟨t, ?_, ?_, memory, input, output⟩
  · rw [body_eq]
    exact .seq (.assign trivial) execution
  · simpa [foldl_step, initialized, State.setReg] using result

/-- The generic measured fold counts the real comparison expression. The two
extra instructions per element, compared with summation, evaluate the target
and compare it with the loaded word. Initialization and the final guard are
also included; no iteration-count annotation is assumed. -/
theorem body_localMeasured {program : Program} {control heapLimit depth : Nat}
    (hw : 0 < w) {s t : State w}
    (execution : SafeExec program heapLimit depth countFunctions.function.count.body s t) :
    LocalMeasuredExec control program heapLimit depth countFunctions.function.count.body
      (18 * (s.regs registers.remaining).toNat + 4) s t := by
  rw [body_eq] at execution ⊢
  cases execution with
  | seq first rest =>
      cases first with
      | assign reads =>
          have loop := Fold.loop_localMeasured registers (control := control) hw rest
          have sequence := LocalMeasuredExec.seq
            (LocalMeasuredExec.assign (control := control) reads) loop
          have steps :
              LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
                  (.assign registers.accumulator (.const 0)) +
                (((value.compile (ABI.scratch control)).length + 12) *
                  ((s.setReg registers.accumulator (s.eval (.const 0))).regs
                    registers.remaining).toNat + 2) =
                18 * (s.regs registers.remaining).toNat + 4 := by
            change 2 + ((6 + 12) * (s.regs registers.remaining).toNat + 2) = _
            omega
          simpa only [steps] using sequence

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
  rintro args entry ⟨rfl, represented⟩
  have hlength : xs.length < 2 ^ w := by omega
  have count :
      ((entry.enter (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)).regs
        Count.registers.remaining).toNat = xs.length := Word.ofNat_toNat_of_lt hlength
  obtain ⟨callee, execution, returned, memory, input, output⟩ :=
    Count.body_safe (program := program) (depth := depth) hw
      (entry.enter (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target))
      base target xs represented.1 rfl count rfl represented.2 hfit
  have restored : entry.restore callee = entry := by
    simp only [State.restore, memory, input, output, State.enter]
  refine ⟨BitVec.ofNat w (xs.count target), entry, ?_, rfl, rfl⟩
  have invocation := FunctionExec.of_body (f := countFunctions.function.count)
    (countFunctions.arguments_length.count ⟨base, BitVec.ofNat w xs.length⟩ target)
    (by decide) execution (by trivial)
  change callee.eval countFunctions.function.count.result =
    BitVec.ofNat w (xs.count target) at returned
  simpa only [returned, restored] using invocation

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
not include an enclosing caller's argument evaluation, frame or return code. -/
theorem count_function_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    FunctionTimeBound control program heapLimit depth countFunctions.function.count
      (fun args entry =>
        args = countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target ∧
        ArrayAt heapLimit base xs entry)
      (fun _ _ => 18 * xs.length + 4) := by
  rintro args entry ⟨rfl, _⟩ steps value finish ⟨_, _, callee, execution, _, _, _⟩
  have hlength : xs.length < 2 ^ w := by omega
  have count :
      ((entry.enter (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)).regs
        Count.registers.remaining).toNat = xs.length := Word.ofNat_toNat_of_lt hlength
  have measured := Count.body_localMeasured (control := control) hw execution.erase
  have same := (execution.deterministic measured).1
  simpa only [count, same] using Nat.le_refl (18 * xs.length + 4)

/-- Correctness and cost describe a single invocation of the declared function. -/
theorem count_function_runs_with_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base target : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    ∃ bodySteps,
      FunctionMeasuredExec control program heapLimit depth countFunctions.function.count
        (countFunctions.arguments.count ⟨base, BitVec.ofNat w xs.length⟩ target)
        bodySteps entry (BitVec.ofNat w (xs.count target)) entry ∧
      bodySteps ≤ 18 * xs.length + 4 := by
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
      (fun _ _ => 18 * xs.length + 4) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish execution
  apply count_function_timeBound (control := control) (program := program) (depth := depth)
    (base := array.base) (target := target) (xs := xs) hw hfit
    (countFunctions.arguments.count array target) entry ?_ steps value finish execution
  refine ⟨?_, represented.2⟩
  simp only [countFunctions.arguments.count, represented.length_eq]

end Ram.Source.Array
