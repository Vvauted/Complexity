/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Complexity.Computability.Ram.Array.Fold
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
word addition; the mathematical list is a specification of existing memory.

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

@[simp] theorem wordSum_nil : wordSum ([] : List (Word w)) = 0 := rfl

@[simp] theorem wordSum_cons (x : Word w) (xs : List (Word w)) :
    wordSum (x :: xs) = x + wordSum xs := by
  simp [wordSum, BitVec.ofNat_add]

/-- Summing a concatenation is ordinary addition of the two modular sums. -/
theorem wordSum_append (xs ys : List (Word w)) :
    wordSum (xs ++ ys) = wordSum xs + wordSum ys := by
  simp [wordSum, List.sum_append, BitVec.ofNat_add]

theorem wordSum_toNat (xs : List (Word w)) :
    (wordSum xs).toNat = (xs.map BitVec.toNat).sum % 2 ^ w := by
  rw [wordSum, BitVec.toNat_ofNat]

/-- A reusable function over an existing array, with no input/output driver. -/
ram_def sumFunctions := ram_functions% {
  fn sum(xs : array) {
    let mut accumulator := 0;
    while xs.length {
      accumulator := accumulator + load[xs.base];
      xs.base := xs.base + 1;
      xs.length := xs.length - 1;
    }
    return accumulator;
  }
  fn sumPair(left : array, right : array) {
    let leftSum ← call sum(left);
    let rightSum ← call sum(right);
    return leftSum + rightSum;
  }
}

namespace Sum

/-- The body of the declared function, also usable as a preloaded block. -/
def block : Stmt := sumFunctions.function.sum.body

/-- The loop selected from the executable declaration. -/
def loop : Stmt :=
  match block with
  | .seq _ loop => loop
  | _ => .skip

/-- The guard selected from the executable declaration. -/
def condition : Expr :=
  match loop with
  | .while condition _ => condition
  | _ => .const 0

/-- The three assignments selected from the executable declaration. -/
def body : Stmt :=
  match loop with
  | .while _ body => body
  | _ => .skip

def sumValue : Expr :=
  match body with
  | .seq (.assign _ value) _ => value
  | _ => .const 0

def nextPointer : Expr :=
  match body with
  | .seq _ (.seq (.assign _ value) _) => value
  | _ => .const 0

def nextCount : Expr :=
  match body with
  | .seq _ (.seq _ (.assign _ value)) => value
  | _ => .const 0

private def foldRegisters : Fold.Registers where
  pointer := sumFunctions.localReg.sum.xs.base
  remaining := sumFunctions.localReg.sum.xs.length
  accumulator := sumFunctions.localReg.sum.accumulator
  pointer_ne_remaining := by decide
  pointer_ne_accumulator := by decide
  remaining_ne_accumulator := by decide

theorem block_wellFormed : block.WellFormed 3 := by
  simp [block, sumFunctions.body_eq.sum, Stmt.WellFormed, Expr.Bounded]

/-- The body has no calls, so its contract is independent of the function table. -/
theorem block_callsValid (program : Program) : Compiler.CallsValid program block := by
  simp [block, sumFunctions.body_eq.sum, Compiler.CallsValid]

/-- Removing the first logical element advances the represented base by one
actual word address. This is the standard array suffix view. -/
theorem arrayRep_tail {mem : Word w → Word w} {base x : Word w}
    {xs : List (Word w)} (hrep : ArrayRep mem base (x :: xs))
    (_hfit : base.toNat + (x :: xs).length < 2 ^ w) :
    ArrayRep mem (base + 1) xs := by
  simpa [arrayAddr] using hrep.drop 1

/-- Exact state transformer of the three source assignments in `body`. -/
def bodyResult (s : Source.State w) : Source.State w :=
  let a := s.setReg 2 (s.eval sumValue)
  let b := a.setReg 0 (a.eval nextPointer)
  b.setReg 1 (b.eval nextCount)

private theorem bodyResult_eq_stepState (s : Source.State w) :
    bodyResult s = Fold.stepState foldRegisters sumValue s := rfl

@[simp] theorem bodyResult_pointer (s : Source.State w) :
    (bodyResult s).regs 0 = s.regs 0 + 1 := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    body, loop, block, sumFunctions.body_eq.sum, Source.State.setReg, Expr.eval, BinOp.eval]

@[simp] theorem bodyResult_count (s : Source.State w) :
    (bodyResult s).regs 1 = s.regs 1 - 1 := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    body, loop, block, sumFunctions.body_eq.sum, Source.State.setReg, Expr.eval, BinOp.eval]

@[simp] theorem bodyResult_sum (s : Source.State w) :
    (bodyResult s).regs 2 = s.regs 2 + s.mem (s.regs 0) := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    body, loop, block, sumFunctions.body_eq.sum, Source.State.setReg, Expr.eval, BinOp.eval]

@[simp] theorem bodyResult_mem (s : Source.State w) : (bodyResult s).mem = s.mem := rfl
@[simp] theorem bodyResult_input (s : Source.State w) : (bodyResult s).input = s.input := rfl
@[simp] theorem bodyResult_output (s : Source.State w) :
    (bodyResult s).outputRev = s.outputRev := rfl

theorem bodyResult_other (s : Source.State w) (r : Reg) (hr : 3 ≤ r) :
    (bodyResult s).regs r = s.regs r := by
  have h0 : r ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 3) hr)
  have h1 : r ≠ 1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 1 < 3) hr)
  have h2 : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 3) hr)
  simp [bodyResult, Source.State.setReg, h0, h1, h2]

/-- Every iteration performs a legal single-word source load. -/
theorem body_safe {program : Program} {H depth : Nat} (s : Source.State w)
    (haddr : (s.regs 0).toNat < H) :
    Source.SafeExec program H depth body s (bodyResult s) := by
  simpa only [bodyResult_eq_stepState] using
    (Fold.body_safe foldRegisters (program := program) (heapLimit := H) (depth := depth)
      (value := sumValue) s ⟨trivial, trivial, haddr⟩)

theorem bodyResult_count_toNat (hw : 0 < w) (s : Source.State w)
    (hz : s.regs 1 ≠ 0) :
    ((bodyResult s).regs 1).toNat = (s.regs 1).toNat - 1 := by
  simpa only [bodyResult_eq_stepState] using
    (Fold.stepState_remaining_toNat foldRegisters (value := sumValue) hw s hz)

-- Ordinary list algebra is the only algorithm-specific induction.
private theorem sum_foldl (xs : List (Word w)) (acc : Word w) :
    xs.foldl (fun a x => a + x) acc = acc + wordSum xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih, wordSum_cons]
      exact BitVec.add_assoc _ _ _

/-- The loop consumes precisely the represented suffix, constructing one
`SafeExec.whileTrue` per list element and a final `whileFalse`. This is a
termination and semantic theorem, not an assigned per-iteration time cost. -/
theorem loop_safe {program : Program} {H depth : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w))
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, Source.SafeExec program H depth loop s t ∧
      t.regs 2 = s.regs 2 + wordSum xs ∧
      t.regs 0 = arrayAddr base xs.length ∧ t.regs 1 = 0 ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, 3 ≤ r → t.regs r = s.regs r := by
  obtain ⟨t, execution, result, pointer, count, _, memory, input, output, other⟩ :=
    Fold.loop_safe foldRegisters (value := sumValue) (program := program) (depth := depth)
      (step := fun acc x => acc + x) (R := fun _ => True) hw
      (by intro current _ address; exact ⟨trivial, trivial, address⟩)
      (by intro current _; rfl) (by intros; trivial)
      s base xs trivial hrep hptr hcount hheap hfit
  refine ⟨t, execution, result.trans (sum_foldl xs _), pointer, count,
    memory, input, output, ?_⟩
  intro r hr
  apply other r
  · have hbound : foldRegisters.pointer < 3 := by decide
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hbound hr))
  · have hbound : foldRegisters.remaining < 3 := by decide
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hbound hr))
  · have hbound : foldRegisters.accumulator < 3 := by decide
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hbound hr))

/-- The fixed block computes the modular array sum for arbitrary preloaded
contents, preserving the full source memory, I/O, and all other registers. -/
theorem block_safe {program : Program} {H depth : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w))
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, Source.SafeExec program H depth block s t ∧
      t.regs 2 = wordSum xs ∧ t.regs 0 = arrayAddr base xs.length ∧ t.regs 1 = 0 ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, 3 ≤ r → t.regs r = s.regs r := by
  let start := s.setReg 2 0
  have hrep' : ArrayRep start.mem base xs := hrep
  have hptr' : start.regs 0 = base := by simpa [start, Source.State.setReg] using hptr
  have hcount' : (start.regs 1).toNat = xs.length := by
    simpa [start, Source.State.setReg] using hcount
  obtain ⟨t, hx, hv, hp, hc, hm, hi, ho, hr⟩ :=
    loop_safe hw start base xs hrep' hptr' hcount' hheap hfit
  refine ⟨t, .seq (.assign trivial) hx, ?_, hp, hc, hm, hi, ho, ?_⟩
  · simpa [start] using hv
  · intro r hbound
    have hne : r ≠ 2 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 2 < 3) hbound)
    exact (hr r hbound).trans (Source.State.setReg_ne s 2 r 0 hne)

/-- The accumulator contains the sum of mathematical element values modulo
`2^w`. No no-overflow assumption is imposed on that sum. -/
theorem block_modular {program : Program} {H depth : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w))
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, Source.SafeExec program H depth block s t ∧
      (t.regs 2).toNat = (xs.map BitVec.toNat).sum % 2 ^ w ∧ t.mem = s.mem := by
  obtain ⟨t, hx, hv, _, _, hm, _, _, _⟩ :=
    block_safe hw s base xs hrep hptr hcount hheap hfit
  exact ⟨t, hx, by rw [hv, wordSum_toNat], hm⟩

theorem body_result {program : Program} {H depth : Nat} {s t : Source.State w}
    (h : Source.SafeExec program H depth body s t) : t = bodyResult s := by
  exact (Fold.body_result foldRegisters (value := sumValue) h).trans
    (bodyResult_eq_stepState s).symm

/-- One iteration's count is the sum of the three emitted assignment blocks. -/
theorem body_localMeasured {program : Program} {control H depth : Nat} {s t : Source.State w}
    (h : Source.SafeExec program H depth body s t) :
    Source.LocalMeasuredExec control program H depth body 13 s t := by
  exact Fold.body_localMeasured (control := control) foldRegisters (value := sumValue) h

/-- Any successful execution of this loop has the derived exact linear count.
The proof follows the actual loop derivation and the strictly decreasing word
counter; it does not assume an iteration count annotation. -/
theorem loop_localMeasured {program : Program} {control H depth : Nat} (hw : 0 < w)
    {s t : Source.State w} (h : Source.SafeExec program H depth loop s t) :
    Source.LocalMeasuredExec control program H depth loop (16 * (s.regs 1).toNat + 2) s t := by
  exact Fold.loop_localMeasured (control := control) foldRegisters (value := sumValue) hw h

/-- Initialization and the final false guard are included in the block count. -/
theorem block_localMeasured {program : Program} {control H depth : Nat} (hw : 0 < w)
    {s t : Source.State w} (h : Source.SafeExec program H depth block s t) :
    Source.LocalMeasuredExec control program H depth block (16 * (s.regs 1).toNat + 4) s t := by
  cases h with
  | seq first rest =>
      cases first with
      | assign reads =>
          have hr := loop_localMeasured (control := control) hw rest
          have hx := Source.LocalMeasuredExec.seq (Source.LocalMeasuredExec.assign reads) hr
          have hcount :
              ((s.setReg 2 (s.eval (.const 0))).regs 1).toNat = (s.regs 1).toNat := rfl
          have hsteps :
              LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
                (.assign 2 (.const 0)) +
              (16 * ((s.setReg 2 (s.eval (.const 0))).regs 1).toNat + 2) =
              16 * (s.regs 1).toNat + 4 := by
            change 2 + (16 * ((s.setReg 2 (s.eval (.const 0))).regs 1).toNat + 2) = _
            rw [hcount]
            omega
          simpa only [hsteps] using hx

end Sum

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
      (fun _ entry value finish => value = wordSum xs ∧ finish = entry) := by
  rintro args entry ⟨rfl, represented⟩
  have hlength : xs.length < 2 ^ w := by omega
  have hcount :
      ((entry.enter (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)).regs 1).toNat =
        xs.length := Word.ofNat_toNat_of_lt hlength
  obtain ⟨callee, body, value, _, _, memory, input, output, _⟩ :=
    Sum.block_safe (program := program) (depth := depth) hw
      (entry.enter (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩))
      base xs represented.1 rfl hcount represented.2 hfit
  have restored : entry.restore callee = entry := by
    simp only [State.restore, memory, input, output, State.enter]
  refine ⟨wordSum xs, entry, ?_, rfl, rfl⟩
  have invocation := FunctionExec.of_body
    (f := sumFunctions.function.sum)
    (sumFunctions.arguments_length.sum ⟨base, BitVec.ofNat w xs.length⟩)
    (by decide) body (by trivial)
  simpa only [sumFunctions.result_eq.sum, State.eval, Expr.eval, value, restored] using invocation

/-- Call array sum directly on represented contents. No caller register, input
stream or output buffer is needed, and every caller state field is preserved. -/
theorem sum_function_runs {w heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
      entry (wordSum xs) entry := by
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
      (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩) entry value finish) :
    value.toNat = (xs.map BitVec.toNat).sum ∧ finish = entry := by
  obtain ⟨result, unchanged⟩ :=
    (sum_function_contract (program := program) (depth := depth) hw hfit).post
      ⟨rfl, represented⟩ execution
  exact ⟨by rw [result, wordSum_toNat, Nat.mod_eq_of_lt hsum], unchanged⟩

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
      (fun _ _ => 16 * xs.length + 4) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish
    ⟨_, _, callee, execution, _, _, _⟩
  have hlength : xs.length < 2 ^ w := by omega
  have hcount :
      ((entry.enter (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)).regs 1).toNat =
        xs.length := Word.ofNat_toNat_of_lt hlength
  have exactExecution := Sum.block_localMeasured (control := control) hw execution.erase
  have count := (execution.deterministic exactExecution).1
  simpa only [hcount, count] using Nat.le_refl (16 * xs.length + 4)

/-- Combining correctness with its separate cost proof yields one invocation
with the same mathematical result, unchanged caller state and actual body count. -/
theorem sum_function_runs_with_timeBound {w control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    ∃ bodySteps,
      FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
        (sumFunctions.arguments.sum ⟨base, BitVec.ofNat w xs.length⟩)
        bodySteps entry (wordSum xs) entry ∧ bodySteps ≤ 16 * xs.length + 4 := by
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
      (fun _ entry value finish => value = wordSum xs ∧ finish = entry) := by
  apply (sum_function_contract (program := program) (depth := depth)
    (base := array.base) (xs := xs) hw hfit).consequence
  · rintro args entry ⟨rfl, represented⟩
    refine ⟨?_, represented.2⟩
    simp only [sumFunctions.arguments.sum, represented.length_eq]
  · intro args entry value finish _ result
    exact result

/-- A typed reference supplies the complete runtime array argument to the same
function invocation, while the list appears only in the specification. -/
theorem sum_function_runs_of_ref {w heapLimit depth : Nat} {program : Program}
    {array : ArrayRef w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : array.base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : array.Rep heapLimit xs entry) :
    FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum array) entry (wordSum xs) entry := by
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
      (sumFunctions.arguments.sum array) (16 * xs.length + 4) entry (wordSum xs) entry := by
  obtain ⟨arity, frame, callee, body, reads, value, finish⟩ :=
    sum_function_runs_of_ref (program := program) (depth := depth) hw hfit entry represented
  refine ⟨arity, frame, callee, ?_, reads, value, finish⟩
  have count : ((entry.enter (sumFunctions.arguments.sum array)).regs 1).toNat =
      xs.length := represented.1
  simpa only [count] using Sum.block_localMeasured (control := control) hw body

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
      (fun _ entry value finish => value = wordSum xs + wordSum ys ∧ finish = entry) := by
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
      (sumFunctions.arguments.sumPair left right) entry (wordSum xs + wordSum ys) entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    sumPair_function_contract (depth := depth) hw leftFit rightFit sumFunctions.function_lookup.sum
      (sumFunctions.arguments.sumPair left right) entry ⟨rfl, leftArray, rightArray⟩
  exact execution

private theorem sum_call_steps (control pointer length bodySteps : Nat) :
    (ABI.callPrefixLocals control sumFunctions.function.sum.locals
      [.var pointer, .var length] 0).length + 1 + bodySteps +
        (ABI.returnCodeLocals control sumFunctions.function.sum.locals
          sumFunctions.function.sum.result).length + 1 = bodySteps + 37 := by
  rw [ABI.callLocals_steps_eq]
  change 2 + bodySteps + 1 + 7 * 3 + 2 + 11 = bodySteps + 37
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
      (sumFunctions.arguments.sumPair left right) (16 * (xs.length + ys.length) + 82)
      entry (wordSum xs + wordSum ys) entry := by
  let entered := entry.enter (sumFunctions.arguments.sumPair left right)
  let middle := entered.setReg sumFunctions.localReg.sumPair.leftSum (wordSum xs)
  have first : FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
      ([.var sumFunctions.localReg.sumPair.left.base,
        .var sumFunctions.localReg.sumPair.left.length].map entered.eval)
      (16 * xs.length + 4) entered (wordSum xs) entered :=
    sum_function_measured_of_ref hw leftFit entered (leftArray.enter _)
  have firstCall := first.call (dst := sumFunctions.localReg.sumPair.leftSum) lookup
    (by simp [Expr.ReadsBelow])
  rw [sum_call_steps] at firstCall
  have second : FunctionMeasuredExec control program heapLimit depth sumFunctions.function.sum
      ([.var sumFunctions.localReg.sumPair.right.base,
        .var sumFunctions.localReg.sumPair.right.length].map middle.eval)
      (16 * ys.length + 4) middle (wordSum ys) middle :=
    sum_function_measured_of_ref hw rightFit middle
      ((rightArray.enter _).setReg sumFunctions.localReg.sumPair.leftSum (wordSum xs))
  have secondCall := second.call (dst := sumFunctions.localReg.sumPair.rightSum) lookup
    (by simp [Expr.ReadsBelow])
  rw [sum_call_steps] at secondCall
  have body : LocalMeasuredExec control program heapLimit (depth + 1)
      sumFunctions.function.sumPair.body (16 * (xs.length + ys.length) + 82)
      entered (middle.setReg sumFunctions.localReg.sumPair.rightSum (wordSum ys)) := by
    rw [sumFunctions.body_eq.sumPair]
    have counts : (16 * xs.length + 4 + 37) + (16 * ys.length + 4 + 37) =
        16 * (xs.length + ys.length) + 82 := by omega
    rw [← counts]
    exact firstCall.seq secondCall
  exact FunctionMeasuredExec.of_body
    (sumFunctions.arguments_length.sumPair left right) (by decide) body ⟨trivial, trivial⟩

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
        Part.some (16 * (xs.length + ys.length) + 82) :=
  (sumPair_function_measured (control := 0) (depth := 0) hw leftFit rightFit lookup
    entry leftArray rightArray).bodyTime_eq_some

end Ram.Source.Array
