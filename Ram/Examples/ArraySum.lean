/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array
import Ram.SafeSource
import Ram.Measured
import Ram.Verification.StateMTraversal

/-!
# A fixed while program summing a preloaded array

Registers 0 and 1 initially hold the array pointer and length. Register 2 is
the accumulator. The program below is fixed: neither its AST nor its compiled
code is unrolled using the input list. The list in the specification is a
logical view of preloaded memory, not a runtime argument to a RAM primitive.

This is a block-level contract, not a complete input/output application. The
block preserves memory and I/O and returns its result in register 2. Address
and length bounds are explicit; values and accumulated sums may wrap modulo
the word range. The final theorems derive an exact linear machine-step count
from this same program's measured execution and the compiler's simulation.
-/

namespace Ram.Examples.ArraySum

def condition : Expr := .var 1
def sumValue : Expr := .bin .add (.var 2) (.load (.var 0))
def nextPointer : Expr := .bin .add (.var 0) (.const 1)
def nextCount : Expr := .bin .sub (.var 1) (.const 1)

def body : Stmt :=
  .seq (.assign 2 sumValue)
    (.seq (.assign 0 nextPointer) (.assign 1 nextCount))

def loop : Stmt := .while condition body

/-- The same fixed source block is used for every array length and word width. -/
def block : Stmt := .seq (.assign 2 (.const 0)) loop

theorem block_wellFormed : block.WellFormed 3 := by
  simp [block, loop, body, condition, sumValue, nextPointer, nextCount,
    Stmt.WellFormed, Expr.Bounded]

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

private theorem shifted_address (base : Word w) (i : Nat) :
    arrayAddr (base + 1) i = arrayAddr base (i + 1) := by
  simp only [arrayAddr, Nat.add_comm i 1, BitVec.ofNat_add]
  exact BitVec.add_assoc _ _ _

/-- Removing the first logical element advances the represented base by one
actual word address, with no modular aliasing at the endpoint. -/
theorem arrayRep_tail {mem : Word w → Word w} {base x : Word w}
    {xs : List (Word w)} (hrep : ArrayRep mem base (x :: xs))
    (hfit : base.toNat + (x :: xs).length < 2 ^ w) :
    ArrayRep mem (base + 1) xs := by
  have hnext : (base + 1).toNat = base.toNat + 1 :=
    arrayAddr_toNat (base := base) (i := 1)
      (by simp only [List.length_cons] at hfit; omega)
  refine ⟨?_, ?_⟩
  · rw [hnext]
    simp only [List.length_cons] at hfit
    omega
  · intro i hi
    rw [shifted_address]
    simpa using hrep.lookup (i + 1) (by simpa using Nat.succ_lt_succ hi)

/-- Exact state transformer of the three source assignments in `body`. -/
def bodyResult (s : Source.State w) : Source.State w :=
  let a := s.setReg 2 (s.eval sumValue)
  let b := a.setReg 0 (a.eval nextPointer)
  b.setReg 1 (b.eval nextCount)

@[simp] theorem bodyResult_pointer (s : Source.State w) :
    (bodyResult s).regs 0 = s.regs 0 + 1 := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    Source.State.setReg, Expr.eval, BinOp.eval]

@[simp] theorem bodyResult_count (s : Source.State w) :
    (bodyResult s).regs 1 = s.regs 1 - 1 := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    Source.State.setReg, Expr.eval, BinOp.eval]

@[simp] theorem bodyResult_sum (s : Source.State w) :
    (bodyResult s).regs 2 = s.regs 2 + s.mem (s.regs 0) := by
  simp [bodyResult, sumValue, nextPointer, nextCount, Source.State.eval,
    Source.State.setReg, Expr.eval, BinOp.eval]

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

/-- The three assignments have their actual generated-code sizes. These are
computed code lengths, not user-chosen operation prices. -/
theorem sum_assignment_size : Compiler.stmtSize 3 (.assign 2 sumValue) = 5 := rfl
theorem pointer_assignment_size : Compiler.stmtSize 3 (.assign 0 nextPointer) = 4 := rfl
theorem count_assignment_size : Compiler.stmtSize 3 (.assign 1 nextCount) = 4 := rfl
theorem initialization_size : Compiler.stmtSize 3 (.assign 2 (.const 0)) = 2 := rfl
theorem condition_code_size : (condition.compile (ABI.scratch 3)).length = 1 := rfl

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
theorem body_measured {program : Program} {H depth : Nat} {s t : Source.State w}
    (h : Source.SafeExec program H depth body s t) :
    Source.MeasuredExec 3 program H depth body 13 s t := by
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
theorem loop_measured {program : Program} {H depth : Nat} (hw : 0 < w)
    {s t : Source.State w} (h : Source.SafeExec program H depth loop s t) :
    Source.MeasuredExec 3 program H depth loop (16 * (s.regs 1).toNat + 2) s t := by
  generalize hc : (s.regs 1).toNat = count
  induction count using Nat.strongRecOn generalizing s t with
  | ind count ih =>
      cases h with
      | whileFalse reads hz =>
          have hzero : count = 0 := by
            rw [← hc]
            exact (Word.toNat_eq_zero_iff _).mpr hz
          have hrun : Source.MeasuredExec 3 program H depth loop 2 s s :=
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
          have hrun := Source.MeasuredExec.whileTrue reads hz (body_measured hb) hrest
          have hsteps : (condition.compile (ABI.scratch 3)).length + 1 + 13 + 1 +
              (16 * ((bodyResult s).regs 1).toNat + 2) = 16 * count + 2 := by
            rw [condition_code_size, hcount', ← hc]
            omega
          simpa only [hsteps] using hrun

/-- Initialization and the final false guard are included in the block count. -/
theorem block_measured {program : Program} {H depth : Nat} (hw : 0 < w)
    {s t : Source.State w} (h : Source.SafeExec program H depth block s t) :
    Source.MeasuredExec 3 program H depth block (16 * (s.regs 1).toNat + 4) s t := by
  cases h with
  | seq first rest =>
      cases first with
      | assign reads =>
          have hr := loop_measured hw rest
          have hx := Source.MeasuredExec.seq (Source.MeasuredExec.assign reads) hr
          have hcount :
              ((s.setReg 2 (s.eval (.const 0))).regs 1).toNat = (s.regs 1).toNat := rfl
          have hsteps : Compiler.stmtSize 3 (.assign 2 (.const 0)) +
              (16 * ((s.setReg 2 (s.eval (.const 0))).regs 1).toNat + 2) =
              16 * (s.regs 1).toNat + 4 := by
            rw [initialization_size, hcount]
            omega
          simpa only [hsteps] using hx

/-- Semantic correctness and the compiler-derived linear count for every
preloaded array satisfying the stated address bounds. -/
theorem block_measured_correct {program : Program} {H depth : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w))
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, Source.MeasuredExec 3 program H depth block (16 * xs.length + 4) s t ∧
      t.regs 2 = wordSum xs ∧ t.regs 0 = arrayAddr base xs.length ∧ t.regs 1 = 0 ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, 3 ≤ r → t.regs r = s.regs r := by
  obtain ⟨t, hx, hrest⟩ := block_safe (program := program) (depth := depth)
    hw s base xs hrep hptr hcount hheap hfit
  exact ⟨t, by simpa only [hcount] using block_measured hw hx, hrest⟩

/-- Fixed linked code. The block-level theorem enters at PC 1 with an already
prepared heap and registers; it does not count or claim an input-loading phase. -/
def machine : Code := Compiler.rawLink 3 [] block

theorem block_code_size : Compiler.stmtSize 3 block = 18 := rfl
theorem machine_code_size : machine.length = 20 := rfl

theorem block_valid : Compiler.Valid 3 [] block := by
  refine ⟨block_wellFormed, ?_, ?_⟩
  · simp [Compiler.CallsValid, block, loop, body]
  · simp

theorem checked_machine : Compiler.compileChecked 3 [] block = some machine :=
  Compiler.compileChecked_some_iff.mpr ⟨block_valid, rfl⟩

/-- The exact linear count is realized by the compiled machine, for arbitrary
preloaded arrays and arbitrary target scratch/private-stack contents consistent
with `Matches`. The endpoint is the linked halt instruction, still unexecuted.
No input parser, array loader, or output writer is included in this block count. -/
theorem block_machine {H : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w)) (start : State w)
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (hmatch : s.Matches H 3 start)
    (hstack : H ≤ (start.regs (ABI.sp 3)).toNat)
    (hpc : start.pc = 1) (hcodefit : machine.length < 2 ^ w) :
    ∃ finish, Exec machine (16 * xs.length + 4) start finish ∧
      finish.regs 2 = wordSum xs ∧ finish.regs 0 = arrayAddr base xs.length ∧
      finish.regs 1 = 0 ∧ HeapEqBelow H start.mem finish.mem ∧
      finish.input = start.input ∧ finish.outputRev = start.outputRev ∧
      finish.pc = 19 ∧ finish.status = .running := by
  obtain ⟨sourceFinal, hx, hv, hp, hc, hm, hi, ho, _⟩ :=
    block_measured_correct (program := []) (depth := 0)
      hw s base xs hrep hptr hcount hheap hfit
  have hsimulation := Compiler.simulate_measured block_valid hcodefit hx block_wellFormed
  have hstackfit : Compiler.StackFits 3 0 start := by
    simpa only [Compiler.StackFits, Nat.zero_mul, Nat.add_zero] using
      (start.regs (ABI.sp 3)).isLt
  have hAt : CodeAt machine start.pc
      (Compiler.compileStmt 3 (Compiler.entry 3 [] block) block start.pc) := by
    rw [hpc]
    exact Compiler.rawLink_main 3 [] block
  obtain ⟨finish, he, hfinal, _, hfinalPC⟩ :=
    hsimulation start hmatch hstack hstackfit hAt
  refine ⟨finish, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfinal.running⟩
  · exact (hfinal.regs 2 (by decide)).symm.trans hv
  · exact (hfinal.regs 0 (by decide)).symm.trans hp
  · exact (hfinal.regs 1 (by decide)).symm.trans hc
  · have hh : HeapEqBelow H s.mem finish.mem := by
      rw [← hm]
      exact hfinal.heap
    exact hmatch.heap.symm.trans hh
  · exact hfinal.input.symm.trans (hi.trans hmatch.input)
  · exact hfinal.output.symm.trans (ho.trans hmatch.output)
  · simpa only [hpc, block_code_size] using hfinalPC

/-- Executing the final halt adds exactly one transition. This is a terminating
preloaded-array computation, not a claim about a complete input/output wrapper. -/
theorem machine_halts {H : Nat} (hw : 0 < w)
    (s : Source.State w) (base : Word w) (xs : List (Word w)) (start : State w)
    (hrep : ArrayRep s.mem base xs) (hptr : s.regs 0 = base)
    (hcount : (s.regs 1).toNat = xs.length)
    (hheap : base.toNat + xs.length ≤ H)
    (hfit : base.toNat + xs.length < 2 ^ w)
    (hmatch : s.Matches H 3 start)
    (hstack : H ≤ (start.regs (ABI.sp 3)).toNat)
    (hpc : start.pc = 1) (hcodefit : machine.length < 2 ^ w) :
    ∃ finish, Exec machine (16 * xs.length + 5) start finish ∧
      finish.status = .halted ∧
      (finish.regs 2).toNat = (xs.map BitVec.toNat).sum % 2 ^ w ∧
      HeapEqBelow H start.mem finish.mem ∧ finish.input = start.input ∧
      finish.outputRev = start.outputRev := by
  obtain ⟨finish, he, hv, _, _, hm, hi, ho, hp, hr⟩ :=
    block_machine hw s base xs start hrep hptr hcount hheap hfit hmatch hstack hpc hcodefit
  have hfetch : machine[finish.pc]? = some .halt := by
    rw [hp]
    rfl
  have hh : Exec machine 1 finish (execInstr .halt finish) :=
    Exec.single (step_of_fetch hr hfetch)
  refine ⟨execInstr .halt finish, ?_, rfl, ?_, hm, hi, ho⟩
  · simpa only [Nat.add_assoc] using he.trans hh
  · change (finish.regs 2).toNat = _
    rw [hv, wordSum_toNat]

end Ram.Examples.ArraySum
