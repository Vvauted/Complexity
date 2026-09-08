/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Sum
import Complexity.Computability.Ram.Compiler.Measured

/-!
# Compiling the reusable array-sum function body

The executable definition and its list-level function contracts live in
`Complexity.Computability.Ram.Array.Sum`. This example compiles that same body
as a preloaded block and proves its exact machine count. It includes no loader,
input parser or output writer; those would be separate executable adapters.

The aliases retain the block-level interface for existing consumers. Register
0 holds the pointer, register 1 the length, and register 2 the block result.
The callable function interface restores caller locals instead.
-/

namespace Ram.Examples.ArraySum

export Ram.Source.Array (wordSum wordSum_nil wordSum_cons wordSum_toNat)

export Ram.Source.Array.Sum
  (condition sumValue nextPointer nextCount body loop block block_wellFormed arrayRep_tail
    bodyResult bodyResult_pointer bodyResult_count bodyResult_sum bodyResult_mem bodyResult_input
    bodyResult_output bodyResult_other body_safe bodyResult_count_toNat loop_safe block_safe
    block_modular body_result)

/-- The three assignments have their actual generated-code sizes. These are
computed code lengths, not user-chosen operation prices. -/
theorem sum_assignment_size : Compiler.stmtSize 3 (.assign 2 sumValue) = 5 := rfl
theorem pointer_assignment_size : Compiler.stmtSize 3 (.assign 0 nextPointer) = 4 := rfl
theorem count_assignment_size : Compiler.stmtSize 3 (.assign 1 nextCount) = 4 := rfl
theorem initialization_size : Compiler.stmtSize 3 (.assign 2 (.const 0)) = 2 := rfl
theorem condition_code_size : (condition.compile (ABI.scratch 3)).length = 1 := rfl

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
          have hrun : Source.MeasuredExec 3 program H depth loop
              ((condition.compile (ABI.scratch 3)).length + 1 + 13 + 1 +
                (16 * ((bodyResult s).regs 1).toNat + 2)) s t :=
            .whileTrue reads hz (body_measured hb) hrest
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
  · exact Source.Array.Sum.block_callsValid []
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
