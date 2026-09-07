/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.ExprCompile
import Ram.Memory
import Ram.Execution.Block
import Ram.Execution.MemoryBounds

/-!
# Actual heap accesses of compiled expressions

Expression compilation emits no stores, so every real execution prefix leaves
the entire heap unchanged. This conclusion follows from the empty actual write
set, not from comparing just the initial and final heaps.

`Expr.ReadsBelow` bounds all addresses accessed by the generated instructions.
The proof follows the existing left-to-right compiler and uses its correctness
theorem to identify each load's address in its actual entry state. In particular,
the right operand's read condition is transported across the left operand's
scratch-register updates; source registers must lie below the destination.

All footprints refer to the existing machine execution inside arbitrary
surrounding code. No alternative evaluator, runner, or access cost is introduced.
-/

namespace Ram.Expr

private theorem compile_instr_heapWrites {e : Expr} {dst : Reg} {instr : Instr}
    (member : instr ∈ e.compile dst) (s : State w) : instr.heapWrites s = ∅ := by
  induction e generalizing dst with
  | const n =>
      simp only [compile, List.mem_singleton] at member
      subst instr
      rfl
  | var x =>
      simp only [compile, List.mem_singleton] at member
      subst instr
      rfl
  | bin op a b ia ib =>
      simp only [compile, List.mem_append, List.mem_singleton] at member
      rcases member with (ha | hb) | rfl
      · exact ia ha
      · exact ib hb
      · rfl
  | load a ih =>
      simp only [compile, List.mem_append, List.mem_singleton] at member
      rcases member with ha | rfl
      · exact ih ha
      · rfl

/-- No store occurs during a compiled expression's actual execution. This does
not require a source-register freshness or heap-read bound. -/
theorem compile_heapWrites_eq_empty {code : Code} {e : Expr} {dst : Reg} {s : State w}
    (atExpr : CodeAt code s.pc (e.compile dst)) (running : s.status = .running) :
    heapWrites code (e.compile dst).length s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  obtain ⟨k, hk, write⟩ :=
    (mem_heapWrites_execBlock_iff atExpr (compile_linear e dst) running address).mp member
  rw [compile_instr_heapWrites (List.getElem_mem hk)] at write
  exact Finset.notMem_empty _ write

/-- Every actual heap access made by a compiled expression satisfies its source
read bound. Since the compiled block has no stores, these are precisely loads. -/
theorem compile_heapAccesses_below {code : Code} {e : Expr} {dst : Reg}
    {s : State w} {limit : Nat} (bounded : e.Bounded dst)
    (reads : e.ReadsBelow limit s.regs s.mem)
    (atExpr : CodeAt code s.pc (e.compile dst)) (running : s.status = .running)
    {address : Word w} (member : address ∈ heapAccesses code (e.compile dst).length s) :
    address.toNat < limit := by
  induction e generalizing dst s with
  | const n =>
      have fetch : code[s.pc]? = some (.const dst n) := atExpr.head
      simp only [compile, List.length_singleton, heapAccesses_one,
        stepHeapAccesses_of_fetch running fetch, Instr.heapAccesses,
        Finset.notMem_empty] at member
  | var x =>
      have fetch : code[s.pc]? = some (.move dst x) := atExpr.head
      simp only [compile, List.length_singleton, heapAccesses_one,
        stepHeapAccesses_of_fetch running fetch, Instr.heapAccesses,
        Finset.notMem_empty] at member
  | bin op a b ia ib =>
      let leftState := execBlock (a.compile dst) s
      let rightState := execBlock (b.compile (dst + 1)) leftState
      have atLeft : CodeAt code s.pc (a.compile dst) := atExpr.append_left.append_left
      have leftRun : Exec code (a.compile dst).length s leftState :=
        compile_exec atLeft running
      have leftCorrect : Compiled a dst s leftState := compile_correct bounded.1 s
      have leftPC : leftState.pc = s.pc + (a.compile dst).length :=
        execBlock_pc _ s (compile_linear a dst)
      have leftRunning : leftState.status = .running := leftCorrect.status.trans running
      have atRight : CodeAt code leftState.pc (b.compile (dst + 1)) := by
        rw [leftPC]
        exact atExpr.append_left.append_right
      have rightRun : Exec code (b.compile (dst + 1)).length leftState rightState :=
        compile_exec atRight leftRunning
      have rightPC : rightState.pc = leftState.pc + (b.compile (dst + 1)).length :=
        execBlock_pc _ leftState (compile_linear b (dst + 1))
      have rightRunning : rightState.status = .running :=
        (execBlock_status _ leftState (compile_linear b (dst + 1))).trans leftRunning
      have atOp : CodeAt code rightState.pc [.binop op dst dst (dst + 1)] := by
        rw [rightPC, leftPC]
        simpa only [List.length_append, Nat.add_assoc] using atExpr.append_right
      have rightReads : b.ReadsBelow limit leftState.regs leftState.mem :=
        readsBelow_congr bounded.2 reads.2
          (fun x hx => (leftCorrect.below x hx).symm)
          (fun addr _ => congrFun leftCorrect.memory.symm addr)
      simp only [compile, List.length_append, List.length_singleton] at member
      rw [heapAccesses_add (leftRun.trans rightRun) 1, Finset.mem_union] at member
      rcases member with operands | operation
      · rw [heapAccesses_add leftRun _, Finset.mem_union] at operands
        rcases operands with leftAccess | rightAccess
        · exact ia bounded.1 reads.1 atLeft running leftAccess
        · exact ib (bounded.2.mono (Nat.le_succ dst)) rightReads atRight
            leftRunning rightAccess
      · rw [heapAccesses_one, stepHeapAccesses_of_fetch rightRunning atOp.head] at operation
        exact (Finset.notMem_empty address operation).elim
  | load a ih =>
      let addressState := execBlock (a.compile dst) s
      have atAddress : CodeAt code s.pc (a.compile dst) := atExpr.append_left
      have addressRun : Exec code (a.compile dst).length s addressState :=
        compile_exec atAddress running
      have addressCorrect : Compiled a dst s addressState := compile_correct (e := a) bounded s
      have addressPC : addressState.pc = s.pc + (a.compile dst).length :=
        execBlock_pc _ s (compile_linear a dst)
      have addressRunning : addressState.status = .running :=
        addressCorrect.status.trans running
      have atLoad : CodeAt code addressState.pc [.load dst dst] := by
        rw [addressPC]
        exact atExpr.append_right
      simp only [compile, List.length_append, List.length_singleton] at member
      rw [heapAccesses_add addressRun 1, Finset.mem_union] at member
      rcases member with inner | loadAccess
      · exact ih bounded reads.1 atAddress running inner
      · rw [heapAccesses_one, stepHeapAccesses_of_fetch addressRunning atLoad.head] at loadAccess
        have addressEq : address = addressState.regs dst := by
          simpa only [Instr.heapAccesses, Finset.mem_singleton] using loadAccess
        rw [addressEq, addressCorrect.value]
        exact reads.2

/-- The read bound also holds on every shorter observation horizon. -/
theorem compile_prefix_heapAccesses_below {code : Code} {e : Expr} {dst : Reg}
    {s : State w} {limit k : Nat} (bounded : e.Bounded dst)
    (reads : e.ReadsBelow limit s.regs s.mem)
    (atExpr : CodeAt code s.pc (e.compile dst)) (running : s.status = .running)
    (hk : k ≤ (e.compile dst).length) {address : Word w}
    (member : address ∈ heapAccesses code k s) : address.toNat < limit :=
  compile_heapAccesses_below bounded reads atExpr running
    (heapAccesses_mono code s hk member)

/-- Every actual expression prefix preserves the entire heap, including the
initial and final states. No final-state equality is used to infer this frame. -/
theorem compile_prefix_mem {code : Code} {e : Expr} {dst : Reg}
    {s current : State w} {k : Nat}
    (atExpr : CodeAt code s.pc (e.compile dst)) (running : s.status = .running)
    (hk : k ≤ (e.compile dst).length) (execution : Exec code k s current) :
    current.mem = s.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk (compile_heapWrites_eq_empty atExpr running)

end Ram.Expr
