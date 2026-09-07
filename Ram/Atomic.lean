/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Effects

/-!
# Simulation of atomic source statements

These rules use generated expression code and real move/load/store/I/O
instructions. They retain the source-visible state relation and older stack
frames. All counts are lengths of the executed blocks or actual single steps.
-/

namespace Ram.Atomic

private theorem scratch_fresh (n : Nat) : n < 2 * n + 5 := by
  omega

private theorem block_simulates {n heapLimit : Nat} {code block : Code}
    {s : Source.State w} {t : State w}
    (hcode : CodeAt code t.pc block) (hlinear : ∀ i ∈ block, i.Linear)
    (hrun : t.status = .running)
    (hmatch : Source.State.Matches heapLimit n s (execBlock block t))
    (hframe : FramePreserved n heapLimit t (execBlock block t)) :
    ∃ u, Exec code block.length t u ∧ Source.State.Matches heapLimit n s u ∧
      FramePreserved n heapLimit t u ∧ u.pc = t.pc + block.length :=
  ⟨_, execBlock_exec hcode hlinear hrun, hmatch, hframe, execBlock_pc block t hlinear⟩

theorem assign {n heapLimit dst : Nat} {code : Code} {s : Source.State w} {t : State w}
    {e : Expr} (h : Source.State.Matches heapLimit n s t)
    (hdst : dst < n) (hb : e.Bounded n) (hs : e.ReadsBelow heapLimit s.regs s.mem)
    (hcode : CodeAt code t.pc (e.compile (ABI.scratch n) ++ [Instr.move dst (ABI.scratch n)])) :
    ∃ u, Exec code (e.compile (ABI.scratch n) ++ [Instr.move dst (ABI.scratch n)]).length t u ∧
      Source.State.Matches heapLimit n (s.setReg dst (s.eval e)) u ∧
      FramePreserved n heapLimit t u ∧
      u.pc = t.pc + (e.compile (ABI.scratch n) ++ [Instr.move dst (ABI.scratch n)]).length := by
  have hns : n ≤ ABI.scratch n := by simp only [ABI.scratch]; omega
  have hsp : ABI.sp n < ABI.scratch n := scratch_fresh n
  have hc := h.compile_expr hb hs hns
  have hf := FramePreserved.compile_expr n heapLimit t (hb.mono hns) hsp
  refine block_simulates hcode ?_ h.running ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with he | rfl
    · exact Expr.compile_linear e _ i he
    · trivial
  · simpa only [execBlock_append, execBlock_cons, execBlock_nil, execInstr, hc.2] using
      (hc.1.setReg dst (s.eval e)).next
  · have hne : ABI.sp n ≠ dst := Ne.symm (Nat.ne_of_lt hdst)
    have hf' := (FramePreserved.setReg (heapLimit := heapLimit)
      (execBlock (e.compile (ABI.scratch n)) t) dst (s.eval e) hne).trans
      (FramePreserved.next n heapLimit _)
    simpa only [execBlock_append, execBlock_cons, execBlock_nil, execInstr, hc.2] using
      hf.trans hf'

theorem write {n heapLimit : Nat} {code : Code} {s : Source.State w} {t : State w}
    {e : Expr} (h : Source.State.Matches heapLimit n s t)
    (hb : e.Bounded n) (hs : e.ReadsBelow heapLimit s.regs s.mem)
    (hcode : CodeAt code t.pc (e.compile (ABI.scratch n) ++ [Instr.write (ABI.scratch n)])) :
    ∃ u, Exec code (e.compile (ABI.scratch n) ++ [Instr.write (ABI.scratch n)]).length t u ∧
      Source.State.Matches heapLimit n { s with outputRev := s.eval e :: s.outputRev } u ∧
      FramePreserved n heapLimit t u ∧
      u.pc = t.pc + (e.compile (ABI.scratch n) ++ [Instr.write (ABI.scratch n)]).length := by
  have hns : n ≤ ABI.scratch n := by simp only [ABI.scratch]; omega
  have hsp : ABI.sp n < ABI.scratch n := scratch_fresh n
  have hc := h.compile_expr hb hs hns
  have hf := FramePreserved.compile_expr n heapLimit t (hb.mono hns) hsp
  refine block_simulates hcode ?_ h.running ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with he | rfl
    · exact Expr.compile_linear e _ i he
    · trivial
  · simpa only [execBlock_append, execBlock_cons, execBlock_nil] using
      hc.1.write (ABI.scratch n) (s.eval e) hc.2
  · have hf' : FramePreserved n heapLimit (execBlock (e.compile (ABI.scratch n)) t)
        (execInstr (.write (ABI.scratch n)) (execBlock (e.compile (ABI.scratch n)) t)) :=
      FramePreserved.of_eq rfl rfl
    simpa only [execBlock_append, execBlock_cons, execBlock_nil] using hf.trans hf'

theorem store {n heapLimit : Nat} {code : Code} {s : Source.State w} {t : State w}
    {address value : Expr} (h : Source.State.Matches heapLimit n s t)
    (ha : address.Bounded n) (hv : value.Bounded n)
    (har : address.ReadsBelow heapLimit s.regs s.mem)
    (hvr : value.ReadsBelow heapLimit s.regs s.mem)
    (hdest : (s.eval address).toNat < heapLimit)
    (hcode : CodeAt code t.pc (address.compile (ABI.scratch n) ++
      value.compile (ABI.scratch n + 1) ++ [Instr.store (ABI.scratch n) (ABI.scratch n + 1)])) :
    ∃ u, Exec code (address.compile (ABI.scratch n) ++
        value.compile (ABI.scratch n + 1) ++ [Instr.store (ABI.scratch n) (ABI.scratch n + 1)]).length t u ∧
      Source.State.Matches heapLimit n (s.setMem (s.eval address) (s.eval value)) u ∧
      FramePreserved n heapLimit t u ∧ u.pc = t.pc + (address.compile (ABI.scratch n) ++
        value.compile (ABI.scratch n + 1) ++ [Instr.store (ABI.scratch n) (ABI.scratch n + 1)]).length := by
  have hns : n ≤ ABI.scratch n := by simp only [ABI.scratch]; omega
  have hns' : n ≤ ABI.scratch n + 1 := by omega
  have hsp : ABI.sp n < ABI.scratch n := scratch_fresh n
  let ta := execBlock (address.compile (ABI.scratch n)) t
  let tv := execBlock (value.compile (ABI.scratch n + 1)) ta
  have hca := h.compile_expr ha har hns
  have hcv := hca.1.compile_expr hv hvr hns'
  have haddr : tv.regs (ABI.scratch n) = s.eval address := by
    exact ((Expr.compile_correct (hv.mono hns') ta).below _
      (Nat.lt_succ_self _)).trans hca.2
  have hval : tv.regs (ABI.scratch n + 1) = s.eval value := hcv.2
  have hfa := FramePreserved.compile_expr n heapLimit t (ha.mono hns) hsp
  have hfv := FramePreserved.compile_expr n heapLimit ta (hv.mono hns')
    (Nat.lt_trans hsp (Nat.lt_succ_self _))
  refine block_simulates hcode ?_ h.running ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with (hia | hiv) | rfl
    · exact Expr.compile_linear address _ i hia
    · exact Expr.compile_linear value _ i hiv
    · trivial
  · have hm := (hcv.1.setMem (s.eval address) (s.eval value)).next
    simp only [execBlock_append, execBlock_cons, execBlock_nil]
    change Source.State.Matches heapLimit n (s.setMem (s.eval address) (s.eval value))
      (execInstr (.store (ABI.scratch n) (ABI.scratch n + 1)) tv)
    simpa only [execInstr, haddr, hval] using hm
  · have hfw := (FramePreserved.setMem (n := n) tv (s.eval address)
      (s.eval value) hdest).trans (FramePreserved.next n heapLimit _)
    simp only [execBlock_append, execBlock_cons, execBlock_nil]
    change FramePreserved n heapLimit t
      (execInstr (.store (ABI.scratch n) (ABI.scratch n + 1)) tv)
    simpa only [execInstr, haddr, hval] using (hfa.trans hfv).trans hfw

theorem read {n heapLimit dst : Nat} {code : Code} {s : Source.State w} {t : State w}
    (h : Source.State.Matches heapLimit n s t) (hdst : dst < n)
    (value : Word w) (rest : List (Word w)) (hi : s.input = value :: rest)
    (hcode : code[t.pc]? = some (.read dst)) :
    ∃ u, Exec code 1 t u ∧
      Source.State.Matches heapLimit n { s.setReg dst value with input := rest } u ∧
      FramePreserved n heapLimit t u ∧ u.pc = t.pc + 1 := by
  have hit : t.input = value :: rest := h.input.symm.trans hi
  refine ⟨execInstr (.read dst) t, Exec.single (step_of_fetch h.running hcode),
    h.read dst value rest hi, ?_, ?_⟩
  · apply FramePreserved.of_eq
    · simp only [execInstr, hit, State.next_regs]
      apply State.setReg_ne
      exact Ne.symm (Nat.ne_of_lt hdst)
    · simp only [execInstr, hit, State.next_mem, State.setReg_mem]
  · simp only [execInstr, hit, State.next_pc, State.setReg_pc]

end Ram.Atomic
