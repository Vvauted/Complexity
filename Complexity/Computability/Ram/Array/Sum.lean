/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Slice
import Complexity.Computability.Ram.Source.Function.Time
import Complexity.Computability.Ram.Source.Named.Declaration
import Complexity.Computability.Ram.Verification.StateM.Traversal

/-!
# A callable function summing a represented array

`sumFunctions` is one named executable function over a pointer and length.
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

theorem wordSum_toNat (xs : List (Word w)) :
    (wordSum xs).toNat = (xs.map BitVec.toNat).sum % 2 ^ w := by
  rw [wordSum, BitVec.toNat_ofNat]

/-- A reusable function over an existing array, with no input/output driver. -/
ram_def sumFunctions := ram_functions% {
  fn sum(pointer, remaining) locals (accumulator) {
    accumulator := 0;
    while remaining {
      accumulator := accumulator + load[pointer];
      pointer := pointer + 1;
      remaining := remaining - 1;
    }
    return accumulator;
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

theorem block_wellFormed : block.WellFormed 3 := by
  simp [block, sumFunctions.body_eq.sum, Stmt.WellFormed, Expr.Bounded]

/-- The body has no calls, so its contract is independent of the function table. -/
theorem block_callsValid (program : Program) : Compiler.CallsValid program block := by
  simp [block, sumFunctions.body_eq.sum, Compiler.CallsValid]

private theorem shifted_address (base : Word w) (i : Nat) :
    arrayAddr (base + 1) i = arrayAddr base (i + 1) := by
  change arrayAddr (arrayAddr base 1) i = arrayAddr base (i + 1)
  rw [arrayAddr_add, Nat.add_comm 1 i]

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
  refine .seq (.assign ?_) (.seq (.assign ?_) (.assign ?_))
  · exact ⟨trivial, trivial, haddr⟩
  · exact ⟨trivial, trivial⟩
  · exact ⟨trivial, trivial⟩

theorem bodyResult_count_toNat (hw : 0 < w) (s : Source.State w)
    (hz : s.regs 1 ≠ 0) :
    ((bodyResult s).regs 1).toNat = (s.regs 1).toNat - 1 := by
  have hp : 0 < (s.regs 1).toNat := Nat.pos_of_ne_zero
    (fun h => hz ((Word.toNat_eq_zero_iff _).mp h))
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  have hle : (1 : Word w).toNat ≤ (s.regs 1).toNat := by
    rw [hone]
    exact hp
  rw [bodyResult_count]
  change (BinOp.eval .sub (s.regs 1) 1).toNat = (s.regs 1).toNat - 1
  rw [BinOp.eval_sub_toNat_of_le _ _ hle, hone]

-- Only the accumulator is native model state. The remaining list describes
-- memory, while the pointer endpoint and untouched state stay in the relation.
private structure LoopRep (H : Nat) (entry : Source.State w) (target : Word w)
    (remaining : List (Word w)) (acc : Word w) (s : Source.State w) : Prop where
  array : ArrayRep s.mem (s.regs 0) remaining
  count : (s.regs 1).toNat = remaining.length
  heap : (s.regs 0).toNat + remaining.length ≤ H
  fit : (s.regs 0).toNat + remaining.length < 2 ^ w
  sum : s.regs 2 = acc
  endpoint : arrayAddr (s.regs 0) remaining.length = target
  mem : s.mem = entry.mem
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev
  other : ∀ r, 3 ≤ r → s.regs r = entry.regs r

private theorem body_refines {program : Program} {H depth : Nat}
    {entry : Source.State w} {target : Word w} (hw : 0 < w)
    (x : Word w) (xs : List (Word w)) :
    Source.Refines program H depth body (LoopRep H entry target (x :: xs))
      (fun result => LoopRep H entry target xs result.2)
      (modify (fun acc => acc + x) : StateM (Word w) PUnit).run := by
  intro acc s represented
  have hnext : (s.regs 0 + 1).toNat = (s.regs 0).toNat + 1 :=
    arrayAddr_toNat (base := s.regs 0) (i := 1)
      (by have := represented.fit; simp only [List.length_cons] at this; omega)
  have hnonzero : s.regs 1 ≠ 0 := by
    intro hz
    have hzero := (Word.toNat_eq_zero_iff (s.regs 1)).mpr hz
    rw [represented.count] at hzero
    simp at hzero
  have hload : s.mem (s.regs 0) = x := by
    simpa [arrayAddr] using represented.array.lookup 0 (by simp)
  refine ⟨bodyResult s, body_safe s ?_, ?_⟩
  · have := represented.heap
    simp only [List.length_cons] at this
    omega
  · change LoopRep H entry target xs (acc + x) (bodyResult s)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, represented.mem,
      represented.input, represented.output, ?_⟩
    · simpa only [bodyResult_mem, bodyResult_pointer] using
        arrayRep_tail represented.array represented.fit
    · rw [bodyResult_count_toNat hw s hnonzero, represented.count]
      simp
    · rw [bodyResult_pointer, hnext]
      have := represented.heap
      simp only [List.length_cons] at this
      omega
    · rw [bodyResult_pointer, hnext]
      have := represented.fit
      simp only [List.length_cons] at this
      omega
    · rw [bodyResult_sum, represented.sum, hload]
    · rw [bodyResult_pointer, shifted_address]
      exact represented.endpoint
    · intro r hr
      exact (bodyResult_other s r hr).trans (represented.other r hr)

-- This is an ordinary native StateM equation; it mentions no RAM execution.
private theorem sum_forM_run (xs : List (Word w)) (acc : Word w) :
    ((List.forM xs (fun x => modify (fun a => a + x)) :
      StateM (Word w) PUnit).run acc).2 = acc + wordSum xs := by
  induction xs generalizing acc with
  | nil =>
      change acc = acc + wordSum []
      simp
  | cons x xs ih =>
      change ((List.forM xs (fun x => modify (fun a => a + x)) :
        StateM (Word w) PUnit).run (acc + x)).2 = acc + wordSum (x :: xs)
      rw [ih, wordSum_cons]
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
  have traversal := Source.Refines.stateM_forM
    (program := program) (heapLimit := H) (depth := depth)
    (condition := condition) (body := body)
    (rep := LoopRep H s (arrayAddr base xs.length))
    (fun x : Word w => modify (fun acc => acc + x))
    (by intros; trivial)
    (by
      intro remaining acc current represented
      change current.regs 1 ≠ 0 ↔ remaining ≠ []
      apply not_congr
      exact (Word.toNat_eq_zero_iff (current.regs 1)).symm.trans
        (by rw [represented.count]; exact List.length_eq_zero_iff))
    (body_refines hw) xs
  have start : LoopRep H s (arrayAddr base xs.length) xs (s.regs 2) s :=
    ⟨by simpa only [hptr] using hrep, hcount,
      by simpa only [hptr] using hheap, by simpa only [hptr] using hfit,
      rfl, by rw [hptr], rfl, rfl, rfl, by intros; rfl⟩
  obtain ⟨t, execution, result⟩ := traversal (s.regs 2) s start
  refine ⟨t, execution, result.sum.trans (sum_forM_run xs (s.regs 2)), ?_, ?_,
    result.mem, result.input, result.output, result.other⟩
  · simpa [arrayAddr] using result.endpoint
  · exact (Word.toNat_eq_zero_iff _).mp result.count

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
  cases h with
  | seq first rest =>
      cases first with
      | assign _ =>
          cases rest with
          | seq second third =>
              cases second with
              | assign _ =>
                  cases third with
                  | assign _ => rfl

/-- One iteration's count is the sum of the three emitted assignment blocks. -/
theorem body_localMeasured {program : Program} {control H depth : Nat} {s t : Source.State w}
    (h : Source.SafeExec program H depth body s t) :
    Source.LocalMeasuredExec control program H depth body 13 s t := by
  cases h with
  | seq first rest =>
      cases first with
      | assign hsum =>
          cases rest with
          | seq second third =>
              cases second with
              | assign hptr =>
                  cases third with
                  | assign hcount =>
                      exact .seq (.assign hsum) (.seq (.assign hptr) (.assign hcount))

/-- Any successful execution of this loop has the derived exact linear count.
The proof follows the actual loop derivation and the strictly decreasing word
counter; it does not assume an iteration count annotation. -/
theorem loop_localMeasured {program : Program} {control H depth : Nat} (hw : 0 < w)
    {s t : Source.State w} (h : Source.SafeExec program H depth loop s t) :
    Source.LocalMeasuredExec control program H depth loop (16 * (s.regs 1).toNat + 2) s t := by
  generalize hc : (s.regs 1).toNat = count
  induction count using Nat.strongRecOn generalizing s t with
  | ind count ih =>
      cases h with
      | whileFalse reads hz =>
          have hzero : count = 0 := by
            rw [← hc]
            exact (Word.toNat_eq_zero_iff _).mpr hz
          have hrun : Source.LocalMeasuredExec control program H depth loop 2 s s :=
            .whileFalse reads hz
          simpa only [hzero, Nat.mul_zero, Nat.zero_add] using hrun
      | whileTrue reads hz hb hr =>
          have hpos : 0 < (s.regs 1).toNat := Nat.pos_of_ne_zero
            (fun he => hz ((Word.toNat_eq_zero_iff _).mp he))
          have hm := body_result hb
          cases hm
          have hcount' : ((bodyResult s).regs 1).toNat = (s.regs 1).toNat - 1 :=
            bodyResult_count_toNat hw s hz
          have hlt : ((bodyResult s).regs 1).toNat < count := by
            rw [hcount', ← hc]
            omega
          have hrest := ih ((bodyResult s).regs 1).toNat hlt hr rfl
          have hrun : Source.LocalMeasuredExec control program H depth loop
              ((condition.compile (ABI.scratch control)).length + 1 + 13 + 1 +
                (16 * ((bodyResult s).regs 1).toNat + 2)) s t :=
            .whileTrue reads hz (body_localMeasured hb) hrest
          have hsteps : (condition.compile (ABI.scratch control)).length + 1 + 13 + 1 +
              (16 * ((bodyResult s).regs 1).toNat + 2) = 16 * count + 2 := by
            change 1 + 1 + 13 + 1 + (16 * ((bodyResult s).regs 1).toNat + 2) = _
            rw [hcount', ← hc]
            omega
          simpa only [hsteps] using hrun

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
        args = sumFunctions.arguments.sum base (BitVec.ofNat w xs.length) ∧
        ArrayAt heapLimit base xs entry)
      (fun _ entry value finish => value = wordSum xs ∧ finish = entry) := by
  rintro args entry ⟨rfl, represented⟩
  have hlength : xs.length < 2 ^ w := by omega
  have hcount :
      ((entry.enter (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))).regs 1).toNat =
        xs.length := Word.ofNat_toNat_of_lt hlength
  obtain ⟨callee, body, value, _, _, memory, input, output, _⟩ :=
    Sum.block_safe (program := program) (depth := depth) hw
      (entry.enter (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length)))
      base xs represented.1 rfl hcount represented.2 hfit
  have restored : entry.restore callee = entry := by
    simp only [State.restore, memory, input, output, State.enter]
  refine ⟨wordSum xs, entry, ?_, rfl, rfl⟩
  have invocation := FunctionExec.of_body
    (f := sumFunctions.function.sum)
    (sumFunctions.arguments_length.sum base (BitVec.ofNat w xs.length))
    (by decide) body (by trivial)
  simpa only [sumFunctions.result_eq.sum, State.eval, Expr.eval, value, restored] using invocation

/-- Call array sum directly on represented contents. No caller register, input
stream or output buffer is needed, and every caller state field is preserved. -/
theorem sum_function_runs {w heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} (hw : 0 < w)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (entry : State w) (represented : ArrayAt heapLimit base xs entry) :
    FunctionExec program heapLimit depth sumFunctions.function.sum
      (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))
      entry (wordSum xs) entry := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    sum_function_contract (program := program) (depth := depth) hw hfit
      (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))
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
      (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length)) entry value finish) :
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
        args = sumFunctions.arguments.sum base (BitVec.ofNat w xs.length) ∧
        ArrayAt heapLimit base xs entry)
      (fun _ _ => 16 * xs.length + 4) := by
  rintro args entry ⟨rfl, represented⟩ steps value finish
    ⟨_, _, callee, execution, _, _, _⟩
  have hlength : xs.length < 2 ^ w := by omega
  have hcount :
      ((entry.enter (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))).regs 1).toNat =
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
        (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))
        bodySteps entry (wordSum xs) entry ∧ bodySteps ≤ 16 * xs.length + 4 := by
  obtain ⟨bodySteps, value, finish, execution, ⟨rfl, rfl⟩, bound⟩ :=
    (sum_function_contract (program := program) (depth := depth) hw hfit).with_timeBound
      (sum_function_timeBound (control := control) hw hfit)
      (sumFunctions.arguments.sum base (BitVec.ofNat w xs.length))
      entry ⟨rfl, represented⟩
  exact ⟨bodySteps, execution, bound⟩

end Ram.Source.Array
