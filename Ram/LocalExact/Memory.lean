/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalExact.MemoryBasic
import Ram.LocalAtomic.Memory

/-!
# Compositional target-address bounds for structured statements

These rules retain the existing exact simulation, source safety premises, and
instruction counts. Their additional conclusion bounds the actual heap-access
set, including accesses made by recursively supplied substatement simulations.

Each composition splits the footprint at real execution endpoints. The frame
theorem identifies the substatement's entry SP with the enclosing entry SP.
Condition expressions stay below the source-heap boundary; executed branches
and jumps have no heap accesses but retain their ordinary machine step counts.
Calls are supplied separately by the calling-convention memory proof.
-/

namespace Ram.LocalCompiler

private theorem heap_lower_of_frame {control heapLimit : Nat} {s t : State w}
    (lower : heapLimit ≤ (s.regs (ABI.sp control)).toNat)
    (frame : FramePreserved control heapLimit s t) :
    heapLimit ≤ (t.regs (ABI.sp control)).toNat := by
  simpa only [frame.sp] using lower

private theorem below_envelope {control heapLimit depth : Nat} {t : State w}
    {address : Word w} (below : address.toNat < heapLimit)
    (lower : heapLimit ≤ (t.regs (ABI.sp control)).toNat) :
    address.toNat < (t.regs (ABI.sp control)).toNat + depth * ABI.frameSize control := by
  omega

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

private theorem guard_accesses_below {control locals heapLimit target : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (bounded : e.Bounded locals) (reads : e.ReadsBelow heapLimit s.regs s.mem)
    (atGuard : CodeAt code t.pc (e.compile (ABI.scratch control)))
    (atBranch : code[(execBlock (e.compile (ABI.scratch control)) t).pc]? =
      some (.branchZero (ABI.scratch control) target))
    {address : Word w}
    (member : address ∈ heapAccesses code ((e.compile (ABI.scratch control)).length + 1) t) :
    address.toNat < heapLimit := by
  have guardRun := Expr.compile_exec atGuard matched.running
  have guardRunning :=
    (execBlock_status _ t (Expr.compile_linear e (ABI.scratch control))).trans matched.running
  rw [heapAccesses_add guardRun 1, heapAccesses_one,
    stepHeapAccesses_of_fetch guardRunning atBranch] at member
  simp only [Instr.heapAccesses, Finset.union_empty] at member
  have fresh : locals ≤ ABI.scratch control := by simp only [ABI.scratch]; omega
  exact Expr.compile_heapAccesses_below (bounded.mono fresh)
    (Expr.readsBelow_congr bounded reads matched.regs matched.heap)
    atGuard matched.running member

/-- Skipping performs no transition and therefore no heap access. -/
theorem simulation_skip_memory {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} :
    SimulationMemory control locals heapLimit code localsTable entries depth .skip 0 s s := by
  refine ⟨simulation_skip_exact, ?_⟩
  intro _ t _ _ _ _ address member
  simp only [heapAccesses_zero, Finset.notMem_empty] at member

/-- Assignment's expression accesses the source heap; its final move is heap-free. -/
theorem simulation_assign_memory {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.assign dst value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationMemory control locals heapLimit code localsTable entries depth (.assign dst value)
      (stmtSize control localsTable (.assign dst value)) s
      (s.setReg dst (s.eval value)) := by
  refine ⟨simulation_assign_exact hwf hr, ?_⟩
  intro hlocals t matched lower _ atStmt address member
  apply below_envelope (lower := lower)
  exact LocalAtomic.assign_heapAccesses_below matched hlocals hwf.2 hr atStmt member

/-- Both store operand evaluations and the actual destination are below the
source heap boundary, hence below the entry-SP envelope. -/
theorem simulation_store_memory {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {address value : Expr}
    (hwf : (Stmt.store address value).WellFormed locals)
    (ha : address.ReadsBelow heapLimit s.regs s.mem)
    (hv : value.ReadsBelow heapLimit s.regs s.mem)
    (hd : (s.eval address).toNat < heapLimit) :
    SimulationMemory control locals heapLimit code localsTable entries depth (.store address value)
      (stmtSize control localsTable (.store address value)) s
      (s.setMem (s.eval address) (s.eval value)) := by
  refine ⟨simulation_store_exact hwf ha hv hd, ?_⟩
  intro hlocals t matched lower _ atStmt accessed member
  apply below_envelope (lower := lower)
  exact LocalAtomic.store_heapAccesses_below matched hlocals hwf.1 hwf.2 ha hv hd atStmt member

/-- Successful source input retains its existing exact simulation; the actual
input instruction makes no heap access. -/
theorem simulation_read_memory {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Word w}
    {rest : List (Word w)} (hwf : (Stmt.read dst).WellFormed locals)
    (hi : s.input = value :: rest) :
    SimulationMemory control locals heapLimit code localsTable entries depth (.read dst) 1 s
      { s.setReg dst value with input := rest } := by
  refine ⟨simulation_read_exact hwf hi, ?_⟩
  intro _ t matched _ _ atStmt address member
  rw [LocalAtomic.read_heapAccesses_eq_empty atStmt matched.running] at member
  exact (Finset.notMem_empty address member).elim

/-- Output retains all expression accesses and makes no additional heap access. -/
theorem simulation_write_memory {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.write value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationMemory control locals heapLimit code localsTable entries depth (.write value)
      (stmtSize control localsTable (.write value)) s
      { s with outputRev := s.eval value :: s.outputRev } := by
  refine ⟨simulation_write_exact hwf hr, ?_⟩
  intro hlocals t matched lower _ atStmt address member
  apply below_envelope (lower := lower)
  exact LocalAtomic.write_heapAccesses_below matched hlocals hwf hr atStmt member

/-- Sequence cuts the real footprint at the first statement's endpoint. Its
preserved SP gives both substatements the same address envelope. -/
theorem simulation_seq_memory {control locals heapLimit depth na nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {a b : Stmt} {s middle s' : Source.State w}
    (first : SimulationMemory control locals heapLimit code localsTable entries depth a na s middle)
    (second : SimulationMemory control locals heapLimit code localsTable entries depth b nb middle s') :
    SimulationMemory control locals heapLimit code localsTable entries depth (.seq a b)
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
  rw [heapAccesses_add firstRun nb, Finset.mem_union] at member
  rcases member with firstAccess | secondAccess
  · exact first.2 hlocals t matched lower fits atStmt.append_left address firstAccess
  · have bound := second.2 hlocals u matchedU (heap_lower_of_frame lower frame)
      (fits.of_frame frame) atSecond address secondAccess
    simpa only [frame.sp] using bound

/-- A true conditional includes its actual guard, chosen body, and skip jump.
Only guard and body can access the heap. -/
theorem simulation_iteTrue_memory {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (body : SimulationMemory control locals heapLimit code localsTable entries depth yes nb s s') :
    SimulationMemory control locals heapLimit code localsTable entries depth (.ite c yes no)
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
  rw [heapAccesses_add (guardRun.trans bodyRun) 1,
    heapAccesses_add guardRun nb, Finset.mem_union, Finset.mem_union] at member
  rcases member with (guardAccess | bodyAccess) | jumpAccess
  · exact below_envelope
      (guard_accesses_below matched hlocals hb hr layout.condition atBranch guardAccess) lower
  · have bound := body.2 hlocals g.next matchedG.next (heap_lower_of_frame lower frameB)
      (fits.of_frame frameB) atBody address bodyAccess
    simpa only [frameB.sp] using bound
  · rw [heapAccesses_one, stepHeapAccesses_of_fetch matchedU.running atJump] at jumpAccess
    exact (Finset.notMem_empty address jumpAccess).elim

/-- A false conditional jumps directly to its selected body; skipped code
does not contribute any hypothetical access. -/
theorem simulation_iteFalse_memory {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0)
    (body : SimulationMemory control locals heapLimit code localsTable entries depth no nb s s') :
    SimulationMemory control locals heapLimit code localsTable entries depth (.ite c yes no)
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
  rw [heapAccesses_add guardRun nb, Finset.mem_union] at member
  rcases member with guardAccess | bodyAccess
  · exact below_envelope
      (guard_accesses_below matched hlocals hb hr layout.condition atBranch guardAccess) lower
  · have bound := body.2 hlocals (g.atPC noStart) (matchedG.atPC noStart)
      (heap_lower_of_frame lower frameB) (fits.of_frame frameB) atBody address bodyAccess
    simpa only [frameB.sp] using bound

/-- A false loop guard contributes the guard evaluation and one heap-free
branch, with no body or back-edge access. -/
theorem simulation_whileFalse_memory {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt} {s : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0) :
    SimulationMemory control locals heapLimit code localsTable entries depth (.while c body)
      ((c.compile (ABI.scratch control)).length + 1) s s := by
  refine ⟨simulation_whileFalse_exact hb hr hz, ?_⟩
  intro hlocals t matched lower _ atStmt address member
  let condCode := c.compile (ABI.scratch control)
  let bodyCode := compileStmt control localsTable entries body (t.pc + condCode.length + 1)
  have atLoop : CodeAt code t.pc (whileCode condCode (ABI.scratch control) bodyCode t.pc) := atStmt
  have layout := whileCode_layout atLoop
  have atBranch : code[(execBlock condCode t).pc]? =
      some (.branchZero (ABI.scratch control) (t.pc + condCode.length + bodyCode.length + 2)) := by
    rw [execBlock_pc _ t (Expr.compile_linear c _)]
    exact layout.test
  exact below_envelope
    (guard_accesses_below matched hlocals hb hr layout.condition atBranch member) lower

/-- A true loop iteration preserves the entry SP before repeating. The bound
therefore composes over the actual guard, body, back edge, and remaining run. -/
theorem simulation_whileTrue_memory {control locals heapLimit depth nb nr : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt}
    {s middle s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (iteration : SimulationMemory control locals heapLimit code localsTable entries
      depth body nb s middle)
    (rest : SimulationMemory control locals heapLimit code localsTable entries
      depth (.while c body) nr middle s') :
    SimulationMemory control locals heapLimit code localsTable entries depth (.while c body)
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
  rw [heapAccesses_add iterationRun nr, Finset.mem_union] at member
  rcases member with iterationAccess | restAccess
  · rw [heapAccesses_add (guardRun.trans bodyRun) 1,
      heapAccesses_add guardRun nb, Finset.mem_union, Finset.mem_union] at iterationAccess
    rcases iterationAccess with (guardAccess | bodyAccess) | jumpAccess
    · exact below_envelope
        (guard_accesses_below matched hlocals hb hr layout.condition atBranch guardAccess) lower
    · have bound := iteration.2 hlocals g.next matchedG.next (heap_lower_of_frame lower frameB)
        (fits.of_frame frameB) atBody address bodyAccess
      simpa only [frameB.sp] using bound
    · rw [heapAccesses_one, stepHeapAccesses_of_fetch matchedU.running atJump] at jumpAccess
      exact (Finset.notMem_empty address jumpAccess).elim
  · have bound := rest.2 hlocals (u.atPC t.pc) (matchedU.atPC t.pc)
      (heap_lower_of_frame lower frameI) (fits.of_frame frameI) atStmt address restAccess
    simpa only [frameI.sp] using bound

end Ram.LocalCompiler
