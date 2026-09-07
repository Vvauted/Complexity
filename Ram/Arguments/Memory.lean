/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Arguments
import Ram.ExprCompile.Memory
import Ram.Execution.Block
import Ram.Execution.MemoryBounds

/-!
# Actual memory footprints of argument buffering and local initialization

Argument expressions only read the source heap, and the buffer moves perform
no heap accesses. The read-bound proof preserves the caller's source registers
between successive expressions. No bound on `start + args.length` is needed
for these footprint statements: every buffer destination is above `control`.
Correctness of the buffered values is a separate property, for which
`evalArgs_correct` retains its explicit buffer-fit hypothesis.

Empty write sets are proved from the actually executed instruction blocks,
not from endpoint memory equality. The existing prefix-frame theorem then
preserves the heap at every real execution prefix. No new runner or observer
is introduced.
-/

namespace Ram.ABI

private theorem evalArgs_cons_layout {code : Code} {control start : Nat}
    {e : Expr} {es : List Expr} {s : State w}
    (atArgs : CodeAt code s.pc (evalArgs control start (e :: es)))
    (running : s.status = .running) :
    let evaluated := execBlock (e.compile (scratch control)) s
    let buffered := execInstr (.move (arg control start) (scratch control)) evaluated
    CodeAt code s.pc (e.compile (scratch control)) ∧
    CodeAt code evaluated.pc [.move (arg control start) (scratch control)] ∧
    CodeAt code buffered.pc (evalArgs control (start + 1) es) ∧
    Exec code ((e.compile (scratch control)).length + 1) s buffered ∧
    evaluated.status = .running ∧ buffered.status = .running := by
  dsimp only
  let evaluated := execBlock (e.compile (scratch control)) s
  let buffered := execInstr (.move (arg control start) (scratch control)) evaluated
  have atExpr : CodeAt code s.pc (e.compile (scratch control)) :=
    atArgs.append_left.append_left
  have expressionRun := Expr.compile_exec atExpr running
  have evaluatedPC : evaluated.pc = s.pc + (e.compile (scratch control)).length :=
    execBlock_pc _ s (e.compile_linear (scratch control))
  have evaluatedRunning : evaluated.status = .running :=
    (execBlock_status _ s (e.compile_linear (scratch control))).trans running
  have atMove : CodeAt code evaluated.pc [.move (arg control start) (scratch control)] := by
    rw [evaluatedPC]
    exact atArgs.append_left.append_right
  have moveRun : Exec code 1 evaluated buffered :=
    Exec.single (step_of_fetch evaluatedRunning atMove.head)
  have bufferedPC : buffered.pc = s.pc + (e.compile (scratch control)).length + 1 := by
    simp only [buffered, execInstr, State.next_pc, State.setReg_pc, evaluatedPC]
  have atTail : CodeAt code buffered.pc (evalArgs control (start + 1) es) := by
    rw [bufferedPC]
    simpa only [List.length_append, List.length_singleton] using atArgs.append_right
  exact ⟨atExpr, atMove, atTail, expressionRun.trans moveRun, evaluatedRunning,
    by simpa only [buffered, execInstr, State.next_status, State.setReg_status]
      using evaluatedRunning⟩

/-- Parameter buffering performs no actual stores, independently of source
read bounds or whether the parameter buffer is large enough. -/
theorem evalArgs_heapWrites_eq_empty {code : Code} {control start : Nat}
    {args : List Expr} {s : State w}
    (atArgs : CodeAt code s.pc (evalArgs control start args))
    (running : s.status = .running) :
    heapWrites code (evalArgs control start args).length s = ∅ := by
  induction args generalizing start s with
  | nil => simp only [evalArgs, List.length_nil, heapWrites_zero]
  | cons e es ih =>
      obtain ⟨atExpr, atMove, atTail, prefixRun, evaluatedRunning, bufferedRunning⟩ :=
        evalArgs_cons_layout atArgs running
      have expressionRun := Expr.compile_exec atExpr running
      simp only [evalArgs, List.length_append, List.length_singleton]
      rw [heapWrites_add prefixRun _, heapWrites_add expressionRun 1,
        Expr.compile_heapWrites_eq_empty atExpr running, heapWrites_one,
        stepHeapWrites_of_fetch evaluatedRunning atMove.head,
        ih atTail bufferedRunning]
      simp only [Instr.heapWrites, Finset.empty_union]

/-- Every actual argument-buffering access is below the supplied source-heap
boundary. The buffer registers need not fit for this memory-only conclusion. -/
theorem evalArgs_heapAccesses_below {code : Code} {control start heapLimit : Nat}
    {args : List Expr} {s : State w}
    (bounded : ∀ e ∈ args, e.Bounded control)
    (reads : ∀ e ∈ args, e.ReadsBelow heapLimit s.regs s.mem)
    (atArgs : CodeAt code s.pc (evalArgs control start args))
    (running : s.status = .running) {address : Word w}
    (member : address ∈ heapAccesses code (evalArgs control start args).length s) :
    address.toNat < heapLimit := by
  induction args generalizing start s with
  | nil => simp only [evalArgs, List.length_nil, heapAccesses_zero, Finset.notMem_empty] at member
  | cons e es ih =>
      let evaluated := execBlock (e.compile (scratch control)) s
      let buffered := execInstr (.move (arg control start) (scratch control)) evaluated
      obtain ⟨atExpr, atMove, atTail, prefixRun, evaluatedRunning, bufferedRunning⟩ :=
        evalArgs_cons_layout atArgs running
      have expressionRun := Expr.compile_exec atExpr running
      have hscratch : control ≤ scratch control := by unfold scratch; omega
      have headBound := bounded e (by simp)
      have headReads := reads e (by simp)
      have tailBound : ∀ x ∈ es, x.Bounded control :=
        fun x hx => bounded x (by simp [hx])
      have correct := Expr.compile_correct (headBound.mono hscratch) s
      have bufferedRegs : ∀ r, r < control → buffered.regs r = s.regs r := by
        intro r hr
        have ne : r ≠ arg control start := by unfold arg; omega
        simpa only [buffered, execInstr, State.next_regs, State.setReg_ne _ _ _ _ ne]
          using correct.below r (hr.trans_le hscratch)
      have bufferedMem : buffered.mem = s.mem := by
        simpa only [buffered, execInstr, State.next_mem, State.setReg_mem]
          using correct.memory
      have tailReads : ∀ x ∈ es, x.ReadsBelow heapLimit buffered.regs buffered.mem := by
        intro x hx
        exact Expr.readsBelow_congr (tailBound x hx) (reads x (by simp [hx]))
          (fun r hr => (bufferedRegs r hr).symm)
          (fun a _ => congrFun bufferedMem.symm a)
      simp only [evalArgs, List.length_append, List.length_singleton] at member
      rw [heapAccesses_add prefixRun _, Finset.mem_union] at member
      rcases member with headAccess | tailAccess
      · rw [heapAccesses_add expressionRun 1, Finset.mem_union] at headAccess
        rcases headAccess with expressionAccess | moveAccess
        · exact Expr.compile_heapAccesses_below (headBound.mono hscratch) headReads
            atExpr running expressionAccess
        · rw [heapAccesses_one, stepHeapAccesses_of_fetch evaluatedRunning atMove.head] at moveAccess
          exact (Finset.notMem_empty address moveAccess).elim
      · exact ih tailBound tailReads atTail bufferedRunning tailAccess

/-- The same bound from an ordinary caller source/target match. The active
caller local bound may be smaller than the global ABI register boundary. -/
theorem evalArgs_heapAccesses_below_of_matches
    {code : Code} {control caller start heapLimit : Nat} {args : List Expr}
    {source : Source.State w} {s : State w}
    (matched : source.Matches heapLimit caller s) (hcaller : caller ≤ control)
    (bounded : ∀ e ∈ args, e.Bounded caller)
    (reads : ∀ e ∈ args, e.ReadsBelow heapLimit source.regs source.mem)
    (atArgs : CodeAt code s.pc (evalArgs control start args)) {address : Word w}
    (member : address ∈ heapAccesses code (evalArgs control start args).length s) :
    address.toNat < heapLimit :=
  evalArgs_heapAccesses_below (fun e he => (bounded e he).mono hcaller)
    (fun e he => Expr.readsBelow_congr (bounded e he) (reads e he) matched.regs matched.heap)
    atArgs matched.running member

/-- Shorter observation horizons satisfy the same heap-read boundary. -/
theorem evalArgs_prefix_heapAccesses_below {code : Code} {control start heapLimit k : Nat}
    {args : List Expr} {s : State w}
    (bounded : ∀ e ∈ args, e.Bounded control)
    (reads : ∀ e ∈ args, e.ReadsBelow heapLimit s.regs s.mem)
    (atArgs : CodeAt code s.pc (evalArgs control start args))
    (running : s.status = .running) (hk : k ≤ (evalArgs control start args).length)
    {address : Word w} (member : address ∈ heapAccesses code k s) :
    address.toNat < heapLimit :=
  evalArgs_heapAccesses_below bounded reads atArgs running (heapAccesses_mono code s hk member)

/-- Every actual buffering prefix preserves the complete heap, because the
whole buffering block's actual write set is empty. -/
theorem evalArgs_prefix_mem {code : Code} {control start k : Nat}
    {args : List Expr} {s current : State w}
    (atArgs : CodeAt code s.pc (evalArgs control start args))
    (running : s.status = .running) (hk : k ≤ (evalArgs control start args).length)
    (execution : Exec code k s current) : current.mem = s.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk (evalArgs_heapWrites_eq_empty atArgs running)

private theorem initLocals_instr_heapAccesses {control params locals : Nat} {instr : Instr}
    (member : instr ∈ initLocals control params locals) (s : State w) :
    instr.heapAccesses s = ∅ := by
  induction locals with
  | zero => simp only [initLocals, List.not_mem_nil] at member
  | succ locals ih =>
      simp only [initLocals, List.mem_append, List.mem_singleton] at member
      rcases member with previous | rfl
      · exact ih previous
      · unfold initLocal
        split <;> rfl

/-- Local initialization executes only register moves and constants: its
actual heap-access set is empty, without parameter-count or frame-fit premises. -/
theorem initLocals_heapAccesses_eq_empty {code : Code} {control params locals : Nat}
    {s : State w} (atLocals : CodeAt code s.pc (initLocals control params locals))
    (running : s.status = .running) :
    heapAccesses code (initLocals control params locals).length s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  obtain ⟨k, hk, access⟩ :=
    (mem_heapAccesses_execBlock_iff atLocals (initLocals_linear control params locals)
      running address).mp member
  rw [initLocals_instr_heapAccesses (List.getElem_mem hk)] at access
  exact Finset.notMem_empty _ access

/-- The empty access set also excludes every actual store. -/
theorem initLocals_heapWrites_eq_empty {code : Code} {control params locals : Nat}
    {s : State w} (atLocals : CodeAt code s.pc (initLocals control params locals))
    (running : s.status = .running) :
    heapWrites code (initLocals control params locals).length s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  have access := heapWrites_subset_accesses code (initLocals control params locals).length s member
  rw [initLocals_heapAccesses_eq_empty atLocals running] at access
  exact Finset.notMem_empty _ access

/-- Every actual initialization prefix preserves the entire heap, including
prefixes in the middle of copying or zeroing the local registers. -/
theorem initLocals_prefix_mem {code : Code} {control params locals k : Nat}
    {s current : State w} (atLocals : CodeAt code s.pc (initLocals control params locals))
    (running : s.status = .running) (hk : k ≤ (initLocals control params locals).length)
    (execution : Exec code k s current) : current.mem = s.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk (initLocals_heapWrites_eq_empty atLocals running)

end Ram.ABI
