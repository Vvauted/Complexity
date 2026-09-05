import Ram.Structural

/-!
# Exact machine-step rules for structured statements

These judgments retain a fixed count of actual RAM transitions. The rules below
obtain it from compiled blocks, control-flow transitions, and the exact counts
of their executed substatements. Source programs contain no ticks or operation
prices. Function calls are connected separately by the concrete ABI theorem.

The count precedes source states in both public judgments. Forgetting the count
recovers the existing result-preserving simulation interface.
-/

namespace Ram.Compiler

/-- The statement's compiled execution with an explicit, exact step count. -/
def StatementRunExact (n heapLimit : Nat) (code : Code) (_entries : Nat → Nat)
    (stmt : Stmt) (steps : Nat) (sourceFinal : Source.State w) (start : State w) : Prop :=
  ∃ finish, Exec code steps start finish ∧
    Source.State.Matches heapLimit n sourceFinal finish ∧
    FramePreserved n heapLimit start finish ∧
    finish.pc = start.pc + stmtSize n stmt

/-- The same exact count applies to every target state matching these source
states; unrelated scratch-register values and private stack contents cannot
change the certified execution. -/
def SimulationExact (n heapLimit : Nat) (code : Code) (entries : Nat → Nat)
    (depth : Nat) (stmt : Stmt) (steps : Nat) (s s' : Source.State w) : Prop :=
  ∀ t, Source.State.Matches heapLimit n s t →
    heapLimit ≤ (t.regs (ABI.sp n)).toNat → StackFits n depth t →
    CodeAt code t.pc (compileStmt n entries stmt t.pc) →
    StatementRunExact n heapLimit code entries stmt steps s' t

theorem StatementRunExact.erase {n heapLimit steps : Nat} {code : Code}
    {entries : Nat → Nat} {stmt : Stmt} {s : Source.State w} {t : State w}
    (h : StatementRunExact n heapLimit code entries stmt steps s t) :
    StatementRun n heapLimit code entries stmt s t := by
  obtain ⟨finish, he, hm, hf, hp⟩ := h
  exact ⟨steps, finish, he, hm, hf, hp⟩

theorem SimulationExact.erase {n heapLimit depth steps : Nat} {code : Code}
    {entries : Nat → Nat} {stmt : Stmt} {s s' : Source.State w}
    (h : SimulationExact n heapLimit code entries depth stmt steps s s') :
    Simulation n heapLimit code entries depth stmt s s' :=
  fun t hm hlo hfit hc => (h t hm hlo hfit hc).erase

private theorem heap_lower_of_frame {n heapLimit : Nat} {s t : State w}
    (h : heapLimit ≤ (s.regs (ABI.sp n)).toNat)
    (hf : FramePreserved n heapLimit s t) :
    heapLimit ≤ (t.regs (ABI.sp n)).toNat := by
  simpa only [hf.sp] using h

private theorem scratch_bound (n : Nat) : n ≤ ABI.scratch n := by
  simp only [ABI.scratch]
  omega

private theorem sp_scratch (n : Nat) : ABI.sp n < ABI.scratch n := by
  change n < 2 * n + 5
  omega

theorem simulation_skip_exact {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} :
    SimulationExact n heapLimit code entries depth .skip 0 s s := by
  intro t hm _ _ _
  exact ⟨t, .refl t, hm, FramePreserved.refl n heapLimit t, by simp⟩

theorem simulation_assign_exact {n heapLimit depth dst : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.assign dst value).WellFormed n)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationExact n heapLimit code entries depth (.assign dst value)
      (stmtSize n (.assign dst value)) s
      (s.setReg dst (s.eval value)) := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.assign hm hwf.1 hwf.2 hr hc
  refine ⟨u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.assign dst value) t.pc]
  exact hp

theorem simulation_store_exact {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {address value : Expr}
    (hwf : (Stmt.store address value).WellFormed n)
    (ha : address.ReadsBelow heapLimit s.regs s.mem)
    (hv : value.ReadsBelow heapLimit s.regs s.mem)
    (hd : (s.eval address).toNat < heapLimit) :
    SimulationExact n heapLimit code entries depth (.store address value)
      (stmtSize n (.store address value)) s
      (s.setMem (s.eval address) (s.eval value)) := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.store hm hwf.1 hwf.2 ha hv hd hc
  refine ⟨u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.store address value) t.pc]
  exact hp

theorem simulation_read_exact {n heapLimit depth dst : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Word w}
    {rest : List (Word w)} (hwf : (Stmt.read dst).WellFormed n)
    (hi : s.input = value :: rest) :
    SimulationExact n heapLimit code entries depth (.read dst) 1 s
      { s.setReg dst value with input := rest } := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.read hm hwf value rest hi hc.head
  exact ⟨u, he, hu, hf, hp⟩

theorem simulation_write_exact {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.write value).WellFormed n)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationExact n heapLimit code entries depth (.write value)
      (stmtSize n (.write value)) s
      { s with outputRev := s.eval value :: s.outputRev } := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.write hm hwf hr hc
  refine ⟨u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.write value) t.pc]
  exact hp

theorem simulation_seq_exact {n heapLimit depth na nb : Nat} {code : Code}
    {entries : Nat → Nat} {a b : Stmt} {s middle s' : Source.State w}
    (first : SimulationExact n heapLimit code entries depth a na s middle)
    (second : SimulationExact n heapLimit code entries depth b nb middle s') :
    SimulationExact n heapLimit code entries depth (.seq a b) (na + nb) s s' := by
  intro t hm hlo hfit hc
  change CodeAt code t.pc (compileStmt n entries a t.pc ++
    compileStmt n entries b (t.pc + (compileStmt n entries a t.pc).length)) at hc
  obtain ⟨u, hea, hmu, hfa, hpa⟩ := first t hm hlo hfit hc.append_left
  have hcb : CodeAt code u.pc (compileStmt n entries b u.pc) := by
    rw [hpa]
    simpa only [compileStmt_length] using hc.append_right
  obtain ⟨v, heb, hmv, hfb, hpb⟩ := second u hmu
    (heap_lower_of_frame hlo hfa) (hfit.of_frame hfa) hcb
  refine ⟨v, hea.trans heb, hmv, hfa.trans hfb, ?_⟩
  simp only [stmtSize_seq, hpb, hpa, Nat.add_assoc]

private theorem guard_properties {n heapLimit : Nat} {s : Source.State w}
    {t : State w} {e : Expr} (hm : Source.State.Matches heapLimit n s t)
    (hb : e.Bounded n) (hr : e.ReadsBelow heapLimit s.regs s.mem) :
    Source.State.Matches heapLimit n s (execBlock (e.compile (ABI.scratch n)) t) ∧
    FramePreserved n heapLimit t (execBlock (e.compile (ABI.scratch n)) t) ∧
    (execBlock (e.compile (ABI.scratch n)) t).regs (ABI.scratch n) = s.eval e ∧
    (execBlock (e.compile (ABI.scratch n)) t).pc =
      t.pc + (e.compile (ABI.scratch n)).length := by
  have he := hm.compile_expr hb hr (scratch_bound n)
  exact ⟨he.1, FramePreserved.compile_expr n heapLimit t
    (hb.mono (scratch_bound n)) (sp_scratch n), he.2,
    execBlock_pc _ t (Expr.compile_linear e _)⟩

theorem simulation_iteTrue_exact {n heapLimit depth nb : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {yes no : Stmt} {s s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (body : SimulationExact n heapLimit code entries depth yes nb s s') :
    SimulationExact n heapLimit code entries depth (.ite c yes no)
      ((c.compile (ABI.scratch n)).length + 1 + nb + 1) s s' := by
  intro t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch n)
  let yesCode := compileStmt n entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt n entries no (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  change CodeAt code t.pc (ifCode condCode (ABI.scratch n) yesCode noCode t.pc) at hc
  have layout := ifCode_layout hc
  obtain ⟨hmg, hfg, hvg, hpg⟩ := guard_properties hm hb hr
  have hfb := hfg.trans (FramePreserved.next n heapLimit g)
  have hcb : CodeAt code g.next.pc (compileStmt n entries yes g.next.pc) := by
    change CodeAt code (g.pc + 1) (compileStmt n entries yes (g.pc + 1))
    rw [hpg]
    exact layout.yesBlock
  obtain ⟨u, heb, hmu, hfu, hpu⟩ := body g.next hmg.next
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hp : u.pc = t.pc + condCode.length + yesCode.length + 1 := by
    have hylen : yesCode.length = stmtSize n yes := compileStmt_length _ _ _ _
    change u.pc = g.pc + 1 + stmtSize n yes at hpu
    rw [hpg] at hpu
    change u.pc = t.pc + (c.compile (ABI.scratch n)).length + yesCode.length + 1
    omega
  have hzg : g.regs (ABI.scratch n) ≠ 0 := by
    rw [hvg]
    exact hz
  let target := t.pc + condCode.length + yesCode.length + noCode.length + 2
  refine ⟨u.atPC target,
    Ram.ifCode_then hc (Expr.compile_linear c _) hm.running hzg heb hp hmu.running,
    hmu.atPC target, (hfb.trans hfu).trans (FramePreserved.atPC n heapLimit u target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_ite]
  simp only [yesCode, noCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_iteFalse_exact {n heapLimit depth nb : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {yes no : Stmt} {s s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0)
    (body : SimulationExact n heapLimit code entries depth no nb s s') :
    SimulationExact n heapLimit code entries depth (.ite c yes no)
      ((c.compile (ABI.scratch n)).length + 1 + nb) s s' := by
  intro t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch n)
  let yesCode := compileStmt n entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt n entries no (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  let noStart := t.pc + condCode.length + yesCode.length + 2
  change CodeAt code t.pc (ifCode condCode (ABI.scratch n) yesCode noCode t.pc) at hc
  have layout := ifCode_layout hc
  obtain ⟨hmg, hfg, hvg, _⟩ := guard_properties hm hb hr
  have hfb := hfg.trans (FramePreserved.atPC n heapLimit g noStart)
  have hcb : CodeAt code (g.atPC noStart).pc
      (compileStmt n entries no (g.atPC noStart).pc) := layout.noBlock
  obtain ⟨u, heb, hmu, hfu, hpu⟩ := body (g.atPC noStart) (hmg.atPC noStart)
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hzg : g.regs (ABI.scratch n) = 0 := hvg.trans hz
  refine ⟨u,
    Ram.ifCode_else hc (Expr.compile_linear c _) hm.running hzg heb,
    hmu, hfb.trans hfu, ?_⟩
  simp only [State.atPC_pc, noStart, yesCode, compileStmt_length, condCode] at hpu
  rw [stmtSize_ite]
  omega

theorem simulation_whileFalse_exact {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {body : Stmt} {s : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0) :
    SimulationExact n heapLimit code entries depth (.while c body)
      ((c.compile (ABI.scratch n)).length + 1) s s := by
  intro t hm _ _ hc
  let condCode := c.compile (ABI.scratch n)
  let bodyCode := compileStmt n entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  let target := t.pc + condCode.length + bodyCode.length + 2
  change CodeAt code t.pc (whileCode condCode (ABI.scratch n) bodyCode t.pc) at hc
  obtain ⟨hmg, hfg, hvg, _⟩ := guard_properties hm hb hr
  have hzg : g.regs (ABI.scratch n) = 0 := hvg.trans hz
  refine ⟨g.atPC target,
    Ram.whileCode_exit hc (Expr.compile_linear c _) hm.running hzg,
    hmg.atPC target, hfg.trans (FramePreserved.atPC n heapLimit g target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_while]
  simp only [bodyCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_whileTrue_exact {n heapLimit depth nb nr : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {body : Stmt} {s middle s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (iteration : SimulationExact n heapLimit code entries depth body nb s middle)
    (rest : SimulationExact n heapLimit code entries depth (.while c body) nr middle s') :
    SimulationExact n heapLimit code entries depth (.while c body)
      ((c.compile (ABI.scratch n)).length + 1 + nb + 1 + nr) s s' := by
  intro t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch n)
  let bodyCode := compileStmt n entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  have hc' : CodeAt code t.pc (whileCode condCode (ABI.scratch n) bodyCode t.pc) := hc
  have layout := whileCode_layout hc'
  obtain ⟨hmg, hfg, hvg, hpg⟩ := guard_properties hm hb hr
  have hfb := hfg.trans (FramePreserved.next n heapLimit g)
  have hcb : CodeAt code g.next.pc (compileStmt n entries body g.next.pc) := by
    change CodeAt code (g.pc + 1) (compileStmt n entries body (g.pc + 1))
    rw [hpg]
    exact layout.bodyBlock
  obtain ⟨u, heb, hmu, hfu, hpu⟩ := iteration g.next hmg.next
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hp : u.pc = t.pc + condCode.length + bodyCode.length + 1 := by
    have hblen : bodyCode.length = stmtSize n body := compileStmt_length _ _ _ _
    change u.pc = g.pc + 1 + stmtSize n body at hpu
    rw [hpg] at hpu
    change u.pc = t.pc + (c.compile (ABI.scratch n)).length + bodyCode.length + 1
    omega
  have hzg : g.regs (ABI.scratch n) ≠ 0 := by
    rw [hvg]
    exact hz
  have hi := Ram.whileCode_iter hc' (Expr.compile_linear c _) hm.running hzg heb hp hmu.running
  have hfi := (hfb.trans hfu).trans (FramePreserved.atPC n heapLimit u t.pc)
  obtain ⟨v, her, hmv, hfv, hpv⟩ := rest (u.atPC t.pc) (hmu.atPC t.pc)
    (heap_lower_of_frame hlo hfi) (hfit.of_frame hfi) hc
  exact ⟨v, hi.trans her, hmv, hfi.trans hfv, hpv⟩

end Ram.Compiler

