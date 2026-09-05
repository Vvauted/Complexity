import Ram.LocalAtomic
import Ram.LocalCompiler
import Ram.Structural

/-!
# Exact simulation with an active local-register bound

The active source locals may occupy only a prefix of the ABI's global register
region. Every rule therefore preserves the higher inactive registers as well
as the stack frame. Counts come from the emitted blocks and actual control-flow
transitions, with no source ticks or user-assigned operation prices.

These compositional rules cover primitive statements and structured control.
Calls are connected separately by the callee-sized ABI proof.
-/

namespace Ram.LocalCompiler

/-- Exact target execution, preserving both the source frame and inactive
registers between `locals` and `control`. -/
def StatementRunExact (control locals heapLimit : Nat) (code : Code)
    (localsTable _entries : Nat → Nat) (stmt : Stmt) (steps : Nat)
    (sourceFinal : Source.State w) (start : State w) : Prop :=
  ∃ finish, Exec code steps start finish ∧
    Source.State.Matches heapLimit locals sourceFinal finish ∧
    FramePreserved control heapLimit start finish ∧
    RegsPreservedAbove control locals start finish ∧
    finish.pc = start.pc + stmtSize control localsTable stmt

/-- The active frame bound and ABI register boundary are separate. Exact
execution is uniform over every matching target state and admissible stack. -/
def SimulationExact (control locals heapLimit : Nat) (code : Code)
    (localsTable entries : Nat → Nat) (depth : Nat) (stmt : Stmt) (steps : Nat)
    (s s' : Source.State w) : Prop :=
  locals ≤ control → ∀ t, Source.State.Matches heapLimit locals s t →
    heapLimit ≤ (t.regs (ABI.sp control)).toNat → Compiler.StackFits control depth t →
    CodeAt code t.pc (compileStmt control localsTable entries stmt t.pc) →
    StatementRunExact control locals heapLimit code localsTable entries stmt steps s' t

@[simp] theorem stmtSize_skip (control : Nat) (localsTable : Nat → Nat) :
    stmtSize control localsTable .skip = 0 := rfl

@[simp] theorem stmtSize_seq (control : Nat) (localsTable : Nat → Nat) (a b : Stmt) :
    stmtSize control localsTable (.seq a b) =
      stmtSize control localsTable a + stmtSize control localsTable b := by
  rw [← compileStmt_length control localsTable (fun _ => 0) (.seq a b) 0]
  simp only [compileStmt, List.length_append, compileStmt_length]

@[simp] theorem stmtSize_ite (control : Nat) (localsTable : Nat → Nat)
    (c : Expr) (yes no : Stmt) :
    stmtSize control localsTable (.ite c yes no) =
      (c.compile (ABI.scratch control)).length + stmtSize control localsTable yes +
        stmtSize control localsTable no + 2 := by
  rw [← compileStmt_length control localsTable (fun _ => 0) (.ite c yes no) 0]
  simp only [compileStmt, ifCode_length, compileStmt_length]

@[simp] theorem stmtSize_while (control : Nat) (localsTable : Nat → Nat)
    (c : Expr) (body : Stmt) :
    stmtSize control localsTable (.while c body) =
      (c.compile (ABI.scratch control)).length + stmtSize control localsTable body + 2 := by
  rw [← compileStmt_length control localsTable (fun _ => 0) (.while c body) 0]
  simp only [compileStmt, whileCode_length, compileStmt_length]

private theorem heap_lower_of_frame {control heapLimit : Nat} {s t : State w}
    (h : heapLimit ≤ (s.regs (ABI.sp control)).toNat)
    (hf : FramePreserved control heapLimit s t) :
    heapLimit ≤ (t.regs (ABI.sp control)).toNat := by
  simpa only [hf.sp] using h

private theorem scratch_bound (control : Nat) : control ≤ ABI.scratch control := by
  simp only [ABI.scratch]
  omega

private theorem scratch_fresh (control : Nat) : control < 2 * control + 5 := by omega

theorem simulation_skip_exact {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} :
    SimulationExact control locals heapLimit code localsTable entries depth .skip 0 s s := by
  intro _ t hm _ _ _
  exact ⟨t, .refl t, hm, FramePreserved.refl control heapLimit t,
    RegsPreservedAbove.refl control locals t, by simp⟩

theorem simulation_assign_exact {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.assign dst value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationExact control locals heapLimit code localsTable entries depth (.assign dst value)
      (stmtSize control localsTable (.assign dst value)) s
      (s.setReg dst (s.eval value)) := by
  intro hlocals t hm _ _ hc
  obtain ⟨u, he, hu, hf, hregs, hp⟩ := LocalAtomic.assign hm hlocals hwf.1 hwf.2 hr hc
  refine ⟨u, he, hu, hf, hregs, ?_⟩
  rw [← compileStmt_length control localsTable entries (.assign dst value) t.pc]
  exact hp

theorem simulation_store_exact {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {address value : Expr}
    (hwf : (Stmt.store address value).WellFormed locals)
    (ha : address.ReadsBelow heapLimit s.regs s.mem)
    (hv : value.ReadsBelow heapLimit s.regs s.mem)
    (hd : (s.eval address).toNat < heapLimit) :
    SimulationExact control locals heapLimit code localsTable entries depth (.store address value)
      (stmtSize control localsTable (.store address value)) s
      (s.setMem (s.eval address) (s.eval value)) := by
  intro hlocals t hm _ _ hc
  obtain ⟨u, he, hu, hf, hregs, hp⟩ :=
    LocalAtomic.store hm hlocals hwf.1 hwf.2 ha hv hd hc
  refine ⟨u, he, hu, hf, hregs, ?_⟩
  rw [← compileStmt_length control localsTable entries (.store address value) t.pc]
  exact hp

theorem simulation_read_exact {control locals heapLimit depth dst : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Word w}
    {rest : List (Word w)} (hwf : (Stmt.read dst).WellFormed locals)
    (hi : s.input = value :: rest) :
    SimulationExact control locals heapLimit code localsTable entries depth (.read dst) 1 s
      { s.setReg dst value with input := rest } := by
  intro hlocals t hm _ _ hc
  obtain ⟨u, he, hu, hf, hregs, hp⟩ := LocalAtomic.read hm hlocals hwf value rest hi hc.head
  exact ⟨u, he, hu, hf, hregs, hp⟩

theorem simulation_write_exact {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.write value).WellFormed locals)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    SimulationExact control locals heapLimit code localsTable entries depth (.write value)
      (stmtSize control localsTable (.write value)) s
      { s with outputRev := s.eval value :: s.outputRev } := by
  intro hlocals t hm _ _ hc
  obtain ⟨u, he, hu, hf, hregs, hp⟩ := LocalAtomic.write hm hlocals hwf hr hc
  refine ⟨u, he, hu, hf, hregs, ?_⟩
  rw [← compileStmt_length control localsTable entries (.write value) t.pc]
  exact hp

theorem simulation_seq_exact {control locals heapLimit depth na nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {a b : Stmt} {s middle s' : Source.State w}
    (first : SimulationExact control locals heapLimit code localsTable entries depth a na s middle)
    (second : SimulationExact control locals heapLimit code localsTable entries depth b nb middle s') :
    SimulationExact control locals heapLimit code localsTable entries depth (.seq a b)
      (na + nb) s s' := by
  intro hlocals t hm hlo hfit hc
  change CodeAt code t.pc (compileStmt control localsTable entries a t.pc ++
    compileStmt control localsTable entries b
      (t.pc + (compileStmt control localsTable entries a t.pc).length)) at hc
  obtain ⟨u, hea, hmu, hfa, hra, hpa⟩ := first hlocals t hm hlo hfit hc.append_left
  have hcb : CodeAt code u.pc (compileStmt control localsTable entries b u.pc) := by
    rw [hpa]
    simpa only [compileStmt_length] using hc.append_right
  obtain ⟨v, heb, hmv, hfb, hrb, hpb⟩ := second hlocals u hmu
    (heap_lower_of_frame hlo hfa) (hfit.of_frame hfa) hcb
  refine ⟨v, hea.trans heb, hmv, hfa.trans hfb, hra.trans hrb, ?_⟩
  simp only [stmtSize_seq, hpb, hpa, Nat.add_assoc]

private theorem guard_properties {control locals heapLimit : Nat} {s : Source.State w}
    {t : State w} {e : Expr} (hm : Source.State.Matches heapLimit locals s t)
    (hlocals : locals ≤ control) (hb : e.Bounded locals)
    (hr : e.ReadsBelow heapLimit s.regs s.mem) :
    Source.State.Matches heapLimit locals s (execBlock (e.compile (ABI.scratch control)) t) ∧
    FramePreserved control heapLimit t (execBlock (e.compile (ABI.scratch control)) t) ∧
    RegsPreservedAbove control locals t (execBlock (e.compile (ABI.scratch control)) t) ∧
    (execBlock (e.compile (ABI.scratch control)) t).regs (ABI.scratch control) = s.eval e ∧
    (execBlock (e.compile (ABI.scratch control)) t).pc =
      t.pc + (e.compile (ABI.scratch control)).length := by
  have hbound : locals ≤ ABI.scratch control := Nat.le_trans hlocals (scratch_bound control)
  have he := hm.compile_expr hb hr hbound
  exact ⟨he.1, FramePreserved.compile_expr control heapLimit t
      (hb.mono hbound) (scratch_fresh control),
    RegsPreservedAbove.compile_expr control locals t (hb.mono hbound) (scratch_bound control),
    he.2, execBlock_pc _ t (Expr.compile_linear e _)⟩

theorem simulation_iteTrue_exact {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (body : SimulationExact control locals heapLimit code localsTable entries depth yes nb s s') :
    SimulationExact control locals heapLimit code localsTable entries depth (.ite c yes no)
      ((c.compile (ABI.scratch control)).length + 1 + nb + 1) s s' := by
  intro hlocals t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch control)
  let yesCode := compileStmt control localsTable entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt control localsTable entries no
    (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  change CodeAt code t.pc (ifCode condCode (ABI.scratch control) yesCode noCode t.pc) at hc
  have layout := ifCode_layout hc
  obtain ⟨hmg, hfg, hrg, hvg, hpg⟩ := guard_properties hm hlocals hb hr
  have hfb := hfg.trans (FramePreserved.next control heapLimit g)
  have hrb := hrg.trans (RegsPreservedAbove.next control locals g)
  have hcb : CodeAt code g.next.pc
      (compileStmt control localsTable entries yes g.next.pc) := by
    change CodeAt code (g.pc + 1)
      (compileStmt control localsTable entries yes (g.pc + 1))
    rw [hpg]
    exact layout.yesBlock
  obtain ⟨u, heb, hmu, hfu, hru, hpu⟩ := body hlocals g.next hmg.next
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hp : u.pc = t.pc + condCode.length + yesCode.length + 1 := by
    have hylen : yesCode.length = stmtSize control localsTable yes :=
      compileStmt_length _ _ _ _ _
    change u.pc = g.pc + 1 + stmtSize control localsTable yes at hpu
    rw [hpg] at hpu
    change u.pc = t.pc + (c.compile (ABI.scratch control)).length + yesCode.length + 1
    omega
  have hzg : g.regs (ABI.scratch control) ≠ 0 := by
    rw [hvg]
    exact hz
  let target := t.pc + condCode.length + yesCode.length + noCode.length + 2
  refine ⟨u.atPC target,
    Ram.ifCode_then hc (Expr.compile_linear c _) hm.running hzg heb hp hmu.running,
    hmu.atPC target,
    (hfb.trans hfu).trans (FramePreserved.atPC control heapLimit u target),
    (hrb.trans hru).trans (RegsPreservedAbove.atPC control locals u target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_ite]
  simp only [yesCode, noCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_iteFalse_exact {control locals heapLimit depth nb : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {yes no : Stmt}
    {s s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0)
    (body : SimulationExact control locals heapLimit code localsTable entries depth no nb s s') :
    SimulationExact control locals heapLimit code localsTable entries depth (.ite c yes no)
      ((c.compile (ABI.scratch control)).length + 1 + nb) s s' := by
  intro hlocals t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch control)
  let yesCode := compileStmt control localsTable entries yes (t.pc + condCode.length + 1)
  let noCode := compileStmt control localsTable entries no
    (t.pc + condCode.length + yesCode.length + 2)
  let g := execBlock condCode t
  let noStart := t.pc + condCode.length + yesCode.length + 2
  change CodeAt code t.pc (ifCode condCode (ABI.scratch control) yesCode noCode t.pc) at hc
  have layout := ifCode_layout hc
  obtain ⟨hmg, hfg, hrg, hvg, _⟩ := guard_properties hm hlocals hb hr
  have hfb := hfg.trans (FramePreserved.atPC control heapLimit g noStart)
  have hrb := hrg.trans (RegsPreservedAbove.atPC control locals g noStart)
  have hcb : CodeAt code (g.atPC noStart).pc
      (compileStmt control localsTable entries no (g.atPC noStart).pc) := layout.noBlock
  obtain ⟨u, heb, hmu, hfu, hru, hpu⟩ := body hlocals (g.atPC noStart) (hmg.atPC noStart)
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hzg : g.regs (ABI.scratch control) = 0 := hvg.trans hz
  refine ⟨u,
    Ram.ifCode_else hc (Expr.compile_linear c _) hm.running hzg heb,
    hmu, hfb.trans hfu, hrb.trans hru, ?_⟩
  simp only [State.atPC_pc, noStart, yesCode, compileStmt_length, condCode] at hpu
  rw [stmtSize_ite]
  omega

theorem simulation_whileFalse_exact {control locals heapLimit depth : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt} {s : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0) :
    SimulationExact control locals heapLimit code localsTable entries depth (.while c body)
      ((c.compile (ABI.scratch control)).length + 1) s s := by
  intro hlocals t hm _ _ hc
  let condCode := c.compile (ABI.scratch control)
  let bodyCode := compileStmt control localsTable entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  let target := t.pc + condCode.length + bodyCode.length + 2
  change CodeAt code t.pc (whileCode condCode (ABI.scratch control) bodyCode t.pc) at hc
  obtain ⟨hmg, hfg, hrg, hvg, _⟩ := guard_properties hm hlocals hb hr
  have hzg : g.regs (ABI.scratch control) = 0 := hvg.trans hz
  refine ⟨g.atPC target,
    Ram.whileCode_exit hc (Expr.compile_linear c _) hm.running hzg,
    hmg.atPC target, hfg.trans (FramePreserved.atPC control heapLimit g target),
    hrg.trans (RegsPreservedAbove.atPC control locals g target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_while]
  simp only [bodyCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_whileTrue_exact {control locals heapLimit depth nb nr : Nat} {code : Code}
    {localsTable entries : Nat → Nat} {c : Expr} {body : Stmt}
    {s middle s' : Source.State w}
    (hb : c.Bounded locals) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (iteration : SimulationExact control locals heapLimit code localsTable entries
      depth body nb s middle)
    (rest : SimulationExact control locals heapLimit code localsTable entries
      depth (.while c body) nr middle s') :
    SimulationExact control locals heapLimit code localsTable entries depth (.while c body)
      ((c.compile (ABI.scratch control)).length + 1 + nb + 1 + nr) s s' := by
  intro hlocals t hm hlo hfit hc
  let condCode := c.compile (ABI.scratch control)
  let bodyCode := compileStmt control localsTable entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  have hc' : CodeAt code t.pc (whileCode condCode (ABI.scratch control) bodyCode t.pc) := hc
  have layout := whileCode_layout hc'
  obtain ⟨hmg, hfg, hrg, hvg, hpg⟩ := guard_properties hm hlocals hb hr
  have hfb := hfg.trans (FramePreserved.next control heapLimit g)
  have hrb := hrg.trans (RegsPreservedAbove.next control locals g)
  have hcb : CodeAt code g.next.pc
      (compileStmt control localsTable entries body g.next.pc) := by
    change CodeAt code (g.pc + 1)
      (compileStmt control localsTable entries body (g.pc + 1))
    rw [hpg]
    exact layout.bodyBlock
  obtain ⟨u, heb, hmu, hfu, hru, hpu⟩ := iteration hlocals g.next hmg.next
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hp : u.pc = t.pc + condCode.length + bodyCode.length + 1 := by
    have hblen : bodyCode.length = stmtSize control localsTable body :=
      compileStmt_length _ _ _ _ _
    change u.pc = g.pc + 1 + stmtSize control localsTable body at hpu
    rw [hpg] at hpu
    change u.pc = t.pc + (c.compile (ABI.scratch control)).length + bodyCode.length + 1
    omega
  have hzg : g.regs (ABI.scratch control) ≠ 0 := by
    rw [hvg]
    exact hz
  have hi := Ram.whileCode_iter hc' (Expr.compile_linear c _) hm.running hzg heb hp hmu.running
  have hfi := (hfb.trans hfu).trans (FramePreserved.atPC control heapLimit u t.pc)
  have hri := (hrb.trans hru).trans (RegsPreservedAbove.atPC control locals u t.pc)
  obtain ⟨v, her, hmv, hfv, hrv, hpv⟩ := rest hlocals (u.atPC t.pc) (hmu.atPC t.pc)
    (heap_lower_of_frame hlo hfi) (hfit.of_frame hfi) hc
  exact ⟨v, hi.trans her, hmv, hfi.trans hfv, hri.trans hrv, hpv⟩

end Ram.LocalCompiler
