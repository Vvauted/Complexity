/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Effects

/-!
# Atomic simulation with a function-local register boundary

`control` determines the ABI register layout, while `locals` is the current
function's active source frame. Expression temporaries still begin at the ABI
scratch register. These rules preserve both older memory frames and registers
between the active local boundary and the control-register boundary.

Execution costs are the lengths of the actual generated blocks, or one real
input instruction. No preservation condition is a runtime check or extra step.
-/

namespace Ram.LocalAtomic

private theorem scratch_bound (control : Nat) : control ≤ ABI.scratch control := by
  simp only [ABI.scratch]
  omega

private theorem sp_scratch (control : Nat) : ABI.sp control < ABI.scratch control := by
  change control < 2 * control + 5
  omega

private theorem block_simulates {control locals heapLimit : Nat} {code block : Code}
    {s : Source.State w} {t : State w}
    (hcode : CodeAt code t.pc block) (hlinear : ∀ i ∈ block, i.Linear)
    (hrun : t.status = .running)
    (hmatch : Source.State.Matches heapLimit locals s (execBlock block t))
    (hframe : FramePreserved control heapLimit t (execBlock block t))
    (hregs : RegsPreservedAbove control locals t (execBlock block t)) :
    ∃ u, Exec code block.length t u ∧ Source.State.Matches heapLimit locals s u ∧
      FramePreserved control heapLimit t u ∧ RegsPreservedAbove control locals t u ∧
      u.pc = t.pc + block.length :=
  ⟨_, execBlock_exec hcode hlinear hrun, hmatch, hframe, hregs,
    execBlock_pc block t hlinear⟩

theorem assign {control locals heapLimit dst : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (h : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (hdst : dst < locals) (hb : e.Bounded locals)
    (hs : e.ReadsBelow heapLimit s.regs s.mem)
    (hcode : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)])) :
    ∃ u, Exec code
        (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]).length t u ∧
      Source.State.Matches heapLimit locals (s.setReg dst (s.eval e)) u ∧
      FramePreserved control heapLimit t u ∧ RegsPreservedAbove control locals t u ∧
      u.pc = t.pc +
        (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]).length := by
  have hcs := scratch_bound control
  have hls := Nat.le_trans hlocals hcs
  have hc := h.compile_expr hb hs hls
  have hf := FramePreserved.compile_expr control heapLimit t (hb.mono hls) (sp_scratch control)
  have hg := RegsPreservedAbove.compile_expr control locals t (hb.mono hls) hcs
  refine block_simulates hcode ?_ h.running ?_ ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with he | rfl
    · exact Expr.compile_linear e _ i he
    · trivial
  · simpa only [execBlock_append, execBlock_cons, execBlock_nil, execInstr, hc.2] using
      (hc.1.setReg dst (s.eval e)).next
  · have hne : ABI.sp control ≠ dst :=
      Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hdst hlocals))
    have hf' := (FramePreserved.setReg (n := control) (heapLimit := heapLimit)
      (execBlock (e.compile (ABI.scratch control)) t) dst (s.eval e) hne).trans
      (FramePreserved.next control heapLimit _)
    simpa only [execBlock_append, execBlock_cons, execBlock_nil, execInstr, hc.2] using
      hf.trans hf'
  · have hg' := (RegsPreservedAbove.setReg (control := control)
      (execBlock (e.compile (ABI.scratch control)) t) dst (s.eval e) hdst).trans
      (RegsPreservedAbove.next control locals _)
    simpa only [execBlock_append, execBlock_cons, execBlock_nil, execInstr, hc.2] using
      hg.trans hg'

theorem write {control locals heapLimit : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (h : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (hb : e.Bounded locals) (hs : e.ReadsBelow heapLimit s.regs s.mem)
    (hcode : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)])) :
    ∃ u, Exec code
        (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]).length t u ∧
      Source.State.Matches heapLimit locals { s with outputRev := s.eval e :: s.outputRev } u ∧
      FramePreserved control heapLimit t u ∧ RegsPreservedAbove control locals t u ∧
      u.pc = t.pc +
        (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]).length := by
  have hcs := scratch_bound control
  have hls := Nat.le_trans hlocals hcs
  have hc := h.compile_expr hb hs hls
  have hf := FramePreserved.compile_expr control heapLimit t (hb.mono hls) (sp_scratch control)
  have hg := RegsPreservedAbove.compile_expr control locals t (hb.mono hls) hcs
  refine block_simulates hcode ?_ h.running ?_ ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with he | rfl
    · exact Expr.compile_linear e _ i he
    · trivial
  · simpa only [execBlock_append, execBlock_cons, execBlock_nil] using
      hc.1.write (ABI.scratch control) (s.eval e) hc.2
  · have hf' : FramePreserved control heapLimit (execBlock (e.compile (ABI.scratch control)) t)
        (execInstr (.write (ABI.scratch control)) (execBlock (e.compile (ABI.scratch control)) t)) :=
      FramePreserved.of_eq rfl rfl
    simpa only [execBlock_append, execBlock_cons, execBlock_nil] using hf.trans hf'
  · have hg' : RegsPreservedAbove control locals (execBlock (e.compile (ABI.scratch control)) t)
        (execInstr (.write (ABI.scratch control)) (execBlock (e.compile (ABI.scratch control)) t)) :=
      RegsPreservedAbove.of_regs_eq rfl
    simpa only [execBlock_append, execBlock_cons, execBlock_nil] using hg.trans hg'

theorem store {control locals heapLimit : Nat} {code : Code}
    {s : Source.State w} {t : State w} {address value : Expr}
    (h : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (ha : address.Bounded locals) (hv : value.Bounded locals)
    (har : address.ReadsBelow heapLimit s.regs s.mem)
    (hvr : value.ReadsBelow heapLimit s.regs s.mem)
    (hdest : (s.eval address).toNat < heapLimit)
    (hcode : CodeAt code t.pc (address.compile (ABI.scratch control) ++
      value.compile (ABI.scratch control + 1) ++
        [Instr.store (ABI.scratch control) (ABI.scratch control + 1)])) :
    ∃ u, Exec code (address.compile (ABI.scratch control) ++
        value.compile (ABI.scratch control + 1) ++
          [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]).length t u ∧
      Source.State.Matches heapLimit locals (s.setMem (s.eval address) (s.eval value)) u ∧
      FramePreserved control heapLimit t u ∧ RegsPreservedAbove control locals t u ∧
      u.pc = t.pc + (address.compile (ABI.scratch control) ++
        value.compile (ABI.scratch control + 1) ++
          [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]).length := by
  have hcs := scratch_bound control
  have hls := Nat.le_trans hlocals hcs
  have hls' : locals ≤ ABI.scratch control + 1 := by omega
  have hcs' : control ≤ ABI.scratch control + 1 := by omega
  have hsp := sp_scratch control
  let ta := execBlock (address.compile (ABI.scratch control)) t
  let tv := execBlock (value.compile (ABI.scratch control + 1)) ta
  have hca := h.compile_expr ha har hls
  have hcv := hca.1.compile_expr hv hvr hls'
  have haddr : tv.regs (ABI.scratch control) = s.eval address := by
    exact ((Expr.compile_correct (hv.mono hls') ta).below _
      (Nat.lt_succ_self _)).trans hca.2
  have hval : tv.regs (ABI.scratch control + 1) = s.eval value := hcv.2
  have hfa := FramePreserved.compile_expr control heapLimit t (ha.mono hls) hsp
  have hfv := FramePreserved.compile_expr control heapLimit ta (hv.mono hls')
    (Nat.lt_trans hsp (Nat.lt_succ_self _))
  have hga := RegsPreservedAbove.compile_expr control locals t (ha.mono hls) hcs
  have hgv := RegsPreservedAbove.compile_expr control locals ta (hv.mono hls') hcs'
  refine block_simulates hcode ?_ h.running ?_ ?_ ?_
  · intro i hi
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with (hia | hiv) | rfl
    · exact Expr.compile_linear address _ i hia
    · exact Expr.compile_linear value _ i hiv
    · trivial
  · have hm := (hcv.1.setMem (s.eval address) (s.eval value)).next
    simp only [execBlock_append, execBlock_cons, execBlock_nil]
    change Source.State.Matches heapLimit locals (s.setMem (s.eval address) (s.eval value))
      (execInstr (.store (ABI.scratch control) (ABI.scratch control + 1)) tv)
    simpa only [execInstr, haddr, hval] using hm
  · have hfw := (FramePreserved.setMem (n := control) tv (s.eval address)
      (s.eval value) hdest).trans (FramePreserved.next control heapLimit _)
    simp only [execBlock_append, execBlock_cons, execBlock_nil]
    change FramePreserved control heapLimit t
      (execInstr (.store (ABI.scratch control) (ABI.scratch control + 1)) tv)
    simpa only [execInstr, haddr, hval] using (hfa.trans hfv).trans hfw
  · have hgw := (RegsPreservedAbove.setMem control locals tv (s.eval address)
      (s.eval value)).trans (RegsPreservedAbove.next control locals _)
    simp only [execBlock_append, execBlock_cons, execBlock_nil]
    change RegsPreservedAbove control locals t
      (execInstr (.store (ABI.scratch control) (ABI.scratch control + 1)) tv)
    simpa only [execInstr, haddr, hval] using (hga.trans hgv).trans hgw

theorem read {control locals heapLimit dst : Nat} {code : Code}
    {s : Source.State w} {t : State w}
    (h : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (hdst : dst < locals) (value : Word w) (rest : List (Word w))
    (hi : s.input = value :: rest) (hcode : code[t.pc]? = some (.read dst)) :
    ∃ u, Exec code 1 t u ∧
      Source.State.Matches heapLimit locals { s.setReg dst value with input := rest } u ∧
      FramePreserved control heapLimit t u ∧ RegsPreservedAbove control locals t u ∧
      u.pc = t.pc + 1 := by
  have hit : t.input = value :: rest := h.input.symm.trans hi
  refine ⟨execInstr (.read dst) t, Exec.single (step_of_fetch h.running hcode),
    h.read dst value rest hi, ?_, ?_, ?_⟩
  · apply FramePreserved.of_eq
    · simp only [execInstr, hit, State.next_regs]
      apply State.setReg_ne
      exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hdst hlocals))
    · simp only [execInstr, hit, State.next_mem, State.setReg_mem]
  · intro r hlo _
    simp only [execInstr, hit, State.next_regs]
    apply State.setReg_ne
    exact Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hdst hlo))
  · simp only [execInstr, hit, State.next_pc, State.setReg_pc]

end Ram.LocalAtomic
