/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Arguments.Basic
import Complexity.Computability.Ram.Compiler.ABI.CodeLength

/-!
# Evaluation of multiple return fields

Return expressions are evaluated in the same callee-local state. Their values
are moved to the scalar return register and the protected argument buffer before
the caller frame is restored. The remaining control registers, source locals,
memory and I/O are unchanged. Each field is evaluated by the existing expression
compiler; the exact execution count is the emitted instruction-list length.
-/

namespace Ram.ABI

/-- Return values buffered outside the source frame, with its local and shared
state preserved. The scalar return register is deliberately excluded from the
preserved control registers. -/
structure ResultsEvaluated (n : Nat) (results : List Expr) (s t : State w) : Prop where
  values : ∀ (i : Nat) (hi : i < results.length),
    t.regs (resultReg n i) = results[i].eval s.regs s.mem
  preserved : ∀ r, r < n + 5 → r ≠ rv n → t.regs r = s.regs r
  memory : t.mem = s.mem
  input : t.input = s.input
  output : t.outputRev = s.outputRev
  status : t.status = s.status

/-- Buffering return fields leaves every source local unchanged. -/
theorem ResultsEvaluated.locals {n : Nat} {results : List Expr} {s t : State w}
    (h : ResultsEvaluated n results s t) (r : Reg) (hr : r < n) :
    t.regs r = s.regs r :=
  h.preserved r (Nat.lt_of_lt_of_le hr (Nat.le_add_right n 5))
    (Nat.ne_of_lt (Nat.lt_trans hr (Nat.lt_succ_self n)))

/-- Evaluate all return fields against the original callee frame. The buffer
capacity counts only fields after the scalar return register. -/
theorem evalResults_correct {n : Nat} {results : List Expr}
    (hfit : results.length - 1 ≤ n) (hbounded : ∀ e ∈ results, e.Bounded n)
    (s : State w) : ResultsEvaluated n results s (execBlock (evalResults n results) s) := by
  cases results with
  | nil =>
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro i hi
        simp at hi
      · intro r _ _
        rfl
  | cons e es =>
      have hn : n ≤ scratch n := by unfold scratch; omega
      have he : e.Bounded n := hbounded e (by simp)
      have hes : ∀ x ∈ es, x.Bounded n := fun x hx => hbounded x (by simp [hx])
      have hc := Expr.compile_correct (he.mono hn) s
      let u := execInstr (.move (rv n) (scratch n))
        (execBlock (e.compile (scratch n)) s)
      have huValue : u.regs (rv n) = e.eval s.regs s.mem := by
        simpa only [u, execInstr, State.next_regs, State.setReg_same] using hc.value
      have huPres : ∀ r, r < scratch n → r ≠ rv n → u.regs r = s.regs r := by
        intro r hr hne
        simpa only [u, execInstr, State.next_regs, State.setReg_ne _ _ _ _ hne] using
          hc.below r hr
      have huLocal : ∀ r, r < n → u.regs r = s.regs r := by
        intro r hr
        change (r : Nat) < n at hr
        apply huPres r (Nat.lt_of_lt_of_le hr hn)
        change (r : Nat) ≠ n + 1
        omega
      have huMem : u.mem = s.mem := by
        simpa only [u, execInstr, State.next_mem, State.setReg_mem] using hc.memory
      have huInput : u.input = s.input := by
        simpa only [u, execInstr, State.next_input, State.setReg_input] using hc.input
      have huOutput : u.outputRev = s.outputRev := by
        simpa only [u, execInstr, State.next_outputRev, State.setReg_outputRev] using hc.output
      have huStatus : u.status = s.status := by
        simpa only [u, execInstr, State.next_status, State.setReg_status] using hc.status
      have ht := evalArgs_correct (n := n) (start := 0) (args := es)
        (by simpa using hfit) hes u
      simp only [evalResults, execBlock_append, execBlock_cons]
      change ResultsEvaluated n (e :: es) s (execBlock (evalArgs n 0 es) u)
      refine ⟨?_, ?_, ht.memory.trans huMem, ht.input.trans huInput,
        ht.output.trans huOutput, ht.status.trans huStatus⟩
      · intro i hi
        cases i with
        | zero =>
            have hp := ht.control (rv n) (by change n + 1 < n + 5; omega)
            simpa only [resultReg_zero, List.getElem_cons_zero] using hp.trans huValue
        | succ i =>
            have hi' : i < es.length := by simpa using hi
            have hv := ht.values i hi'
            have hev := Expr.eval_congr (hes es[i] (List.getElem_mem hi')) huLocal huMem
            simpa only [resultReg_succ, Nat.zero_add, List.getElem_cons_succ] using hv.trans hev
      · intro r hr hne
        change (r : Nat) < n + 5 at hr
        exact (ht.control r hr).trans (huPres r (by change (r : Nat) < 2 * n + 5; omega) hne)

/-- Every emitted return-field instruction is straight-line code. -/
theorem evalResults_linear (n : Nat) (results : List Expr) :
    ∀ i ∈ evalResults n results, Instr.Linear i := by
  cases results with
  | nil => simp [evalResults]
  | cons e es =>
      intro i hi
      simp only [evalResults, List.mem_append, List.mem_cons] at hi
      rcases hi with he | rfl | ht
      · exact e.compile_linear (scratch n) i he
      · trivial
      · exact evalArgs_linear n 0 es i ht

/-- Return fields execute with exactly the generated number of instructions. -/
theorem evalResults_exec {code : Code} {n : Nat} {results : List Expr} {s : State w}
    (hcode : CodeAt code s.pc (evalResults n results)) (hrun : s.status = .running) :
    Exec code (evalResults n results).length s (execBlock (evalResults n results) s) :=
  execBlock_exec hcode (evalResults_linear n results) hrun

/-- Return-field evaluation charges every expression and its individual move. -/
theorem evalResults_length (n : Nat) (results : List Expr) :
    (evalResults n results).length =
      (results.map (fun e => (e.compile (scratch n)).length)).sum + results.length := by
  cases results with
  | nil => rfl
  | cons e es =>
      simp only [evalResults, List.length_append, List.length_cons, evalArgs_length,
        List.map_cons, List.sum_cons]
      omega

/-- Return buffering preserves a source match even when the callee uses fewer
locals than the program-wide register bound. -/
theorem ResultsEvaluated.matches {n locals heapLimit : Nat} {results : List Expr}
    {source : Source.State w} {s t : State w}
    (h : ResultsEvaluated n results s t) (hlocal : locals ≤ n)
    (hs : source.Matches heapLimit locals s) : source.Matches heapLimit locals t := by
  refine ⟨?_, ?_, hs.input.trans h.input.symm, hs.output.trans h.output.symm,
    h.status.trans hs.running⟩
  · intro r hr
    exact (hs.regs r hr).trans (h.locals r (Nat.lt_of_lt_of_le hr hlocal)).symm
  · rw [h.memory]
    exact hs.heap

/-- Interpret buffered fields using a source-local match and the actual
expressions' heap-read safety, without equating private stack memory. -/
theorem ResultsEvaluated.source_values {n locals heapLimit : Nat} {results : List Expr}
    {source : Source.State w} {s t : State w}
    (h : ResultsEvaluated n results s t) (hs : source.Matches heapLimit locals s)
    (hb : ∀ e ∈ results, e.Bounded locals)
    (hr : ∀ e ∈ results, e.ReadsBelow heapLimit source.regs source.mem)
    (i : Nat) (hi : i < results.length) :
    t.regs (resultReg n i) = source.eval results[i] := by
  exact (h.values i hi).trans
    (hs.eval_eq (hb _ (List.getElem_mem hi)) (hr _ (List.getElem_mem hi))).symm

end Ram.ABI
