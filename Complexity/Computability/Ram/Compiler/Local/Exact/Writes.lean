/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Atomic.Memory
import Complexity.Computability.Ram.Compiler.Local.Exact.WritesBasic

/-!
# Compositional exclusion of older frames from actual writes

These rules retain the existing exact execution and source safety premises.
Every actual write lies either in the source heap or at/above the real entry
SP, so no address in an older frame can be written during any execution prefix.

The proof splits the existing cumulative write set at actual execution
endpoints. Source stores write below the heap boundary; expression evaluation,
register assignment, input/output, branches, and jumps have empty write sets.
Substatements may call functions, so their right-hand alternative is preserved
using the existing frame theorem's equality of entry and exit SP.

No absence of intermediate writes is inferred from endpoint memory equality.
Calls are connected separately by the calling-convention write proof.
-/

namespace Ram.LocalCompiler

private theorem heap_lower_of_frame {control heapLimit : Nat} {s t : State w}
    (lower : heapLimit ≤ (s.regs (ABI.sp control)).toNat)
    (frame : FramePreserved control heapLimit s t) :
    heapLimit ≤ (t.regs (ABI.sp control)).toNat := by
  simpa only [frame.sp] using lower

private theorem guard_properties {control locals heapLimit : Nat} {s : Source.State w}
    {t : State w} {e : Expr} (matched : Source.State.Matches heapLimit locals s t)
    (hlocals : locals ≤ control) (bounded : e.Bounded locals)
    (reads : e.ReadsBelow heapLimit s.regs s.mem) :
    Source.State.Matches heapLimit locals s (execBlock (e.compile (ABI.scratch control)) t) ∧
    FramePreserved control heapLimit t (execBlock (e.compile (ABI.scratch control)) t) ∧
    (execBlock (e.compile (ABI.scratch control)) t).regs (ABI.scratch control) = s.eval e ∧
    (execBlock (e.compile (ABI.scratch control)) t).pc =
      t.pc + (e.compile (ABI.scratch control)).length := by
  have fresh : locals ≤ ABI.scratch control := by simp only [ABI.scratch]; omega
  have spFresh : ABI.sp control < ABI.scratch control := by
    change control < 2 * control + 5
    omega
  have evaluated := matched.compile_expr bounded reads fresh
  exact ⟨evaluated.1, FramePreserved.compile_expr control heapLimit t
    (bounded.mono fresh) spFresh, evaluated.2,
    execBlock_pc _ t (Expr.compile_linear e _)⟩

private theorem guard_writes_empty {control target : Nat} {code : Code}
    {t : State w} {e : Expr}
    (atGuard : CodeAt code t.pc (e.compile (ABI.scratch control)))
    (running : t.status = .running)
    (atBranch : code[(execBlock (e.compile (ABI.scratch control)) t).pc]? =
      some (.branchZero (ABI.scratch control) target)) :
    heapWrites code ((e.compile (ABI.scratch control)).length + 1) t = ∅ := by
  have guardRun := Expr.compile_exec atGuard running
  have guardRunning :=
    (execBlock_status _ t (Expr.compile_linear e (ABI.scratch control))).trans running
  rw [heapWrites_add guardRun 1, Expr.compile_heapWrites_eq_empty atGuard running,
    heapWrites_one, stepHeapWrites_of_fetch guardRunning atBranch]
  simp only [Instr.heapWrites, Finset.empty_union]

/-- Skipping performs no transition and therefore no heap write. -/
theorem simulation_skip_writes {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} :
    SimulationWrites control locals heapLimit code localsTable entries depth .skip 0 s s := by
  refine ⟨simulation_skip_exact, ?_⟩
  intro _ t _ _ _ _ address member
  simp only [heapWrites_zero, Finset.notMem_empty] at member

/-- Neither expression evaluation nor the final register move writes the heap. -/
theorem simulation_assign_writes {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.assign dst value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationWrites control locals heapLimit code localsTable entries depth (.assign dst value)
      (stmtSize control localsTable (.assign dst value)) s
      (s.setReg dst (s.eval value)) := by
  refine ⟨simulation_assign_exact hwf hr, ?_⟩
  intro _ t matched _ _ atStmt address member
  change address ∈ heapWrites code
    (value.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]).length t
    at member
  rw [LocalAtomic.assign_heapWrites_eq_empty atStmt matched.running] at member
  exact (Finset.notMem_empty address member).elim

/-- The actual store writes exactly its source address, below the heap boundary. -/
theorem simulation_store_writes {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {address value : Expr}
    (hwf : (Stmt.store address value).WellFormed locals)
    (ha : address.ReadsBelow heapLimit s.regs s.mem)
    (hv : value.ReadsBelow heapLimit s.regs s.mem)
    (hd : (s.eval address).toNat < heapLimit) :
    SimulationWrites control locals heapLimit code localsTable entries depth (.store address value)
      (stmtSize control localsTable (.store address value)) s
      (s.setMem (s.eval address) (s.eval value)) := by
  refine ⟨simulation_store_exact hwf ha hv hd, ?_⟩
  intro hlocals t matched _ _ atStmt accessed member
  change accessed ∈ heapWrites code (address.compile (ABI.scratch control) ++
    value.compile (ABI.scratch control + 1) ++
      [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]).length t at member
  rw [LocalAtomic.store_heapWrites_eq_singleton matched hlocals hwf.1 hwf.2 ha atStmt,
    Finset.mem_singleton] at member
  subst accessed
  exact Or.inl hd

/-- Successful source input retains its exact execution and has no heap writes. -/
theorem simulation_read_writes {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Word w}
    {rest : List (Word w)} (hwf : (Stmt.read dst).WellFormed locals)
    (hi : s.input = value :: rest) :
    SimulationWrites control locals heapLimit code localsTable entries depth (.read dst) 1 s
      { s.setReg dst value with input := rest } := by
  refine ⟨simulation_read_exact hwf hi, ?_⟩
  intro _ t matched _ _ atStmt address member
  rw [LocalAtomic.read_heapWrites_eq_empty atStmt matched.running] at member
  exact (Finset.notMem_empty address member).elim

/-- Neither output-expression evaluation nor stream output writes the heap. -/
theorem simulation_write_writes {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.write value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationWrites control locals heapLimit code localsTable entries depth (.write value)
      (stmtSize control localsTable (.write value)) s
      { s with outputRev := s.eval value :: s.outputRev } := by
  refine ⟨simulation_write_exact hwf hr, ?_⟩
  intro _ t matched _ _ atStmt address member
  change address ∈ heapWrites code
    (value.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]).length t
    at member
  rw [LocalAtomic.write_heapWrites_eq_empty atStmt matched.running] at member
  exact (Finset.notMem_empty address member).elim

/-- Sequence cuts the real write set at the first statement's endpoint. Its
preserved SP lets both substatements exclude the same older-frame interval. -/
theorem simulation_seq_writes {control locals heapLimit depth na nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {a b : Stmt} {s middle s' : Source.State w}
    (first : SimulationWrites control locals heapLimit code localsTable entries depth a na s middle)
    (second : SimulationWrites control locals heapLimit code localsTable entries depth b nb middle s') :
    SimulationWrites control locals heapLimit code localsTable entries depth (.seq a b)
      (na + nb) s s' := by
  refine ⟨simulation_seq_exact first.1 second.1, ?_⟩
  intro hlocals t matched lower fits atStmt address member
  change CodeAt code t.pc (compileStmt control localsTable entries a t.pc ++
    compileStmt control localsTable entries b
      (t.pc + (compileStmt control localsTable entries a t.pc).length)) at atStmt
  obtain ⟨u, firstRun, matchedU, frame, _, pc⟩ :=
    first.1 hlocals t matched lower fits atStmt.append_left
  have atSecond : CodeAt code u.pc (compileStmt control localsTable entries b u.pc) := by
    rw [pc]
    simpa only [compileStmt_length] using atStmt.append_right
  rw [heapWrites_add firstRun nb, Finset.mem_union] at member
  rcases member with firstAccess | secondAccess
  · exact first.2 hlocals t matched lower fits atStmt.append_left address firstAccess
  · have bound := second.2 hlocals u matchedU (heap_lower_of_frame lower frame)
      (fits.of_frame frame) atSecond address secondAccess
    simpa only [frame.sp] using bound

/-- A true conditional includes its guard and skip jump in the real step count,
but only its selected body can write the heap. -/
theorem simulation_iteTrue_writes {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (body : SimulationWrites control locals heapLimit code localsTable entries depth yes nb s s') :
    SimulationWrites control locals heapLimit code localsTable entries depth (.ite c yes no)
      ((c.compile (ABI.scratch control)).length + 1 + nb + 1) s s' := by
  refine ⟨simulation_iteTrue_exact hb hr hz body.1, ?_⟩
  intro hlocals t matched lower fits atStmt address member
  let condCode := c.compile (ABI.scratch control)
  let yesCode := compileStmt control localsTable entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt control localsTable entries no
    (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  change CodeAt code t.pc (ifCode condCode (ABI.scratch control) yesCode noCode t.pc) at atStmt
  have layout := ifCode_layout atStmt
  obtain ⟨matchedG, frameG, valueG, pcG⟩ := guard_properties matched hlocals hb hr
  have frameB := frameG.trans (FramePreserved.next control heapLimit g)
  have atBranch : code[g.pc]? =
      some (.branchZero (ABI.scratch control) (t.pc + condCode.length + yesCode.length + 2)) := by
    rw [pcG]
    exact layout.test
  have nonzero : g.regs (ABI.scratch control) ≠ 0 := by rw [valueG]; exact hz
  have guardRun : Exec code (condCode.length + 1) t g.next :=
    (Expr.compile_exec layout.condition matched.running).trans
      (Exec.branchZero_ne_zero matchedG.running atBranch nonzero)
  have atBody : CodeAt code g.next.pc (compileStmt control localsTable entries yes g.next.pc) := by
    change CodeAt code (g.pc + 1) (compileStmt control localsTable entries yes (g.pc + 1))
    rw [pcG]
    exact layout.yesBlock
  obtain ⟨u, bodyRun, matchedU, _, _, pcU⟩ := body.1 hlocals g.next matchedG.next
    (heap_lower_of_frame lower frameB) (fits.of_frame frameB) atBody
  have endPC : u.pc = t.pc + condCode.length + yesCode.length + 1 := by
    have bodyLength : yesCode.length = stmtSize control localsTable yes :=
      compileStmt_length _ _ _ _ _
    change u.pc = g.pc + 1 + stmtSize control localsTable yes at pcU
    rw [pcG] at pcU
    change u.pc = t.pc + (c.compile (ABI.scratch control)).length + yesCode.length + 1
    omega
  have atJump : code[u.pc]? =
      some (.jump (t.pc + condCode.length + yesCode.length + noCode.length + 2)) := by
    rw [endPC]
    exact layout.skip
  rw [heapWrites_add (guardRun.trans bodyRun) 1,
    heapWrites_add guardRun nb, Finset.mem_union, Finset.mem_union] at member
  rcases member with (guardAccess | bodyAccess) | jumpAccess
  · rw [guard_writes_empty layout.condition matched.running atBranch] at guardAccess
    exact (Finset.notMem_empty address guardAccess).elim
  · have bound := body.2 hlocals g.next matchedG.next (heap_lower_of_frame lower frameB)
      (fits.of_frame frameB) atBody address bodyAccess
    simpa only [frameB.sp] using bound
  · rw [heapWrites_one, stepHeapWrites_of_fetch matchedU.running atJump] at jumpAccess
    exact (Finset.notMem_empty address jumpAccess).elim

/-- A false conditional jumps directly to its selected body; neither the
guard nor the skipped branch contributes a write. -/
theorem simulation_iteFalse_writes {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0)
    (body : SimulationWrites control locals heapLimit code localsTable entries depth no nb s s') :
    SimulationWrites control locals heapLimit code localsTable entries depth (.ite c yes no)
      ((c.compile (ABI.scratch control)).length + 1 + nb) s s' := by
  refine ⟨simulation_iteFalse_exact hb hr hz body.1, ?_⟩
  intro hlocals t matched lower fits atStmt address member
  let condCode := c.compile (ABI.scratch control)
  let yesCode := compileStmt control localsTable entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt control localsTable entries no
    (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  let noStart := t.pc + condCode.length + yesCode.length + 2
  change CodeAt code t.pc (ifCode condCode (ABI.scratch control) yesCode noCode t.pc) at atStmt
  have layout := ifCode_layout atStmt
  obtain ⟨matchedG, frameG, valueG, pcG⟩ := guard_properties matched hlocals hb hr
  have frameB := frameG.trans (FramePreserved.atPC control heapLimit g noStart)
  have atBranch : code[g.pc]? = some (.branchZero (ABI.scratch control) noStart) := by
    rw [pcG]
    exact layout.test
  have zero : g.regs (ABI.scratch control) = 0 := valueG.trans hz
  have guardRun : Exec code (condCode.length + 1) t (g.atPC noStart) :=
    (Expr.compile_exec layout.condition matched.running).trans
      (Exec.branchZero_zero matchedG.running atBranch zero)
  have atBody : CodeAt code (g.atPC noStart).pc
      (compileStmt control localsTable entries no (g.atPC noStart).pc) := layout.noBlock
  rw [heapWrites_add guardRun nb, Finset.mem_union] at member
  rcases member with guardAccess | bodyAccess
  · rw [guard_writes_empty layout.condition matched.running atBranch] at guardAccess
    exact (Finset.notMem_empty address guardAccess).elim
  · have bound := body.2 hlocals (g.atPC noStart) (matchedG.atPC noStart)
      (heap_lower_of_frame lower frameB) (fits.of_frame frameB) atBody address bodyAccess
    simpa only [frameB.sp] using bound

/-- A false loop guard executes no body, and its entire real write set is empty. -/
theorem simulation_whileFalse_writes {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt} {s : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0) :
    SimulationWrites control locals heapLimit code localsTable entries depth (.while c body)
      ((c.compile (ABI.scratch control)).length + 1) s s := by
  refine ⟨simulation_whileFalse_exact hb hr hz, ?_⟩
  intro _ t matched _ _ atStmt address member
  let condCode := c.compile (ABI.scratch control)
  let bodyCode := compileStmt control localsTable entries body (t.pc + condCode.length + 1)
  have atLoop : CodeAt code t.pc (whileCode condCode (ABI.scratch control) bodyCode t.pc) := atStmt
  have layout := whileCode_layout atLoop
  have atBranch : code[(execBlock condCode t).pc]? =
      some (.branchZero (ABI.scratch control) (t.pc + condCode.length + bodyCode.length + 2)) := by
    rw [execBlock_pc _ t (Expr.compile_linear c _)]
    exact layout.test
  rw [guard_writes_empty layout.condition matched.running atBranch] at member
  exact (Finset.notMem_empty address member).elim

/-- A true iteration restores the entry SP before repeating, so its body and
remaining execution exclude the same older frames from their actual writes. -/
theorem simulation_whileTrue_writes {control locals heapLimit depth nb nr : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt}
    {s middle s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (iteration : SimulationWrites control locals heapLimit code localsTable entries
      depth body nb s middle)
    (rest : SimulationWrites control locals heapLimit code localsTable entries
      depth (.while c body) nr middle s') :
    SimulationWrites control locals heapLimit code localsTable entries depth (.while c body)
      ((c.compile (ABI.scratch control)).length + 1 + nb + 1 + nr) s s' := by
  refine ⟨simulation_whileTrue_exact hb hr hz iteration.1 rest.1, ?_⟩
  intro hlocals t matched lower fits atStmt address member
  let condCode := c.compile (ABI.scratch control)
  let bodyCode := compileStmt control localsTable entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  have atLoop : CodeAt code t.pc (whileCode condCode (ABI.scratch control) bodyCode t.pc) := atStmt
  have layout := whileCode_layout atLoop
  obtain ⟨matchedG, frameG, valueG, pcG⟩ := guard_properties matched hlocals hb hr
  have frameB := frameG.trans (FramePreserved.next control heapLimit g)
  have atBranch : code[g.pc]? =
      some (.branchZero (ABI.scratch control) (t.pc + condCode.length + bodyCode.length + 2)) := by
    rw [pcG]
    exact layout.test
  have nonzero : g.regs (ABI.scratch control) ≠ 0 := by rw [valueG]; exact hz
  have guardRun : Exec code (condCode.length + 1) t g.next :=
    (Expr.compile_exec layout.condition matched.running).trans
      (Exec.branchZero_ne_zero matchedG.running atBranch nonzero)
  have atBody : CodeAt code g.next.pc (compileStmt control localsTable entries body g.next.pc) := by
    change CodeAt code (g.pc + 1) (compileStmt control localsTable entries body (g.pc + 1))
    rw [pcG]
    exact layout.bodyBlock
  obtain ⟨u, bodyRun, matchedU, frameU, _, pcU⟩ := iteration.1 hlocals g.next matchedG.next
    (heap_lower_of_frame lower frameB) (fits.of_frame frameB) atBody
  have endPC : u.pc = t.pc + condCode.length + bodyCode.length + 1 := by
    have bodyLength : bodyCode.length = stmtSize control localsTable body :=
      compileStmt_length _ _ _ _ _
    change u.pc = g.pc + 1 + stmtSize control localsTable body at pcU
    rw [pcG] at pcU
    change u.pc = t.pc + (c.compile (ABI.scratch control)).length + bodyCode.length + 1
    omega
  have atJump : code[u.pc]? = some (.jump t.pc) := by rw [endPC]; exact layout.back
  have iterationRun := Ram.whileCode_iter atLoop (Expr.compile_linear c _)
    matched.running nonzero bodyRun endPC matchedU.running
  have frameI := (frameB.trans frameU).trans (FramePreserved.atPC control heapLimit u t.pc)
  rw [heapWrites_add iterationRun nr, Finset.mem_union] at member
  rcases member with iterationAccess | restAccess
  · rw [heapWrites_add (guardRun.trans bodyRun) 1,
      heapWrites_add guardRun nb, Finset.mem_union, Finset.mem_union] at iterationAccess
    rcases iterationAccess with (guardAccess | bodyAccess) | jumpAccess
    · rw [guard_writes_empty layout.condition matched.running atBranch] at guardAccess
      exact (Finset.notMem_empty address guardAccess).elim
    · have bound := iteration.2 hlocals g.next matchedG.next (heap_lower_of_frame lower frameB)
        (fits.of_frame frameB) atBody address bodyAccess
      simpa only [frameB.sp] using bound
    · rw [heapWrites_one, stepHeapWrites_of_fetch matchedU.running atJump] at jumpAccess
      exact (Finset.notMem_empty address jumpAccess).elim
  · have bound := rest.2 hlocals (u.atPC t.pc) (matchedU.atPC t.pc)
      (heap_lower_of_frame lower frameI) (fits.of_frame frameI) atStmt address restAccess
    simpa only [frameI.sp] using bound

end Ram.LocalCompiler
