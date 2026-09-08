/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Atomic
import Complexity.Computability.Ram.Compiler.Basic
import Complexity.Computability.Ram.Source.Safe

/-!
# Structural simulation with an explicit call-composition premise

Sequencing, branching, and finite loop execution compose real target-machine
executions. `CallsSimulate` is an explicit theorem premise to be discharged by
the calling-convention proof and induction on call depth. Nothing in this file
assumes that an unproved function call is one machine step.
-/

namespace Ram

theorem Stmt.WellFormed.mono {stmt : Stmt} {n m : Nat}
    (h : stmt.WellFormed n) (hnm : n ≤ m) : stmt.WellFormed m := by
  induction stmt with
  | skip => trivial
  | assign => exact ⟨Nat.lt_of_lt_of_le h.1 hnm, h.2.mono hnm⟩
  | store => exact ⟨h.1.mono hnm, h.2.mono hnm⟩
  | seq _ _ first second => exact ⟨first h.1, second h.2⟩
  | ite _ _ _ yes no => exact ⟨h.1.mono hnm, yes h.2.1, no h.2.2⟩
  | «while» _ _ body => exact ⟨h.1.mono hnm, body h.2⟩
  | read => exact Nat.lt_of_lt_of_le h hnm
  | write => exact Expr.Bounded.mono h hnm
  | call =>
      exact ⟨fun dst hd => Nat.lt_of_lt_of_le (h.1 dst hd) hnm,
        fun e he => (h.2 e he).mono hnm⟩

namespace Compiler

/-- Enough nonwrapping stack space for the maximum nested call depth. -/
def StackFits (n depth : Nat) (t : State w) : Prop :=
  (t.regs (ABI.sp n)).toNat + depth * ABI.frameSize n < 2 ^ w

/-- A real finite machine execution reaches the end of the generated block,
preserving its source result, its entry SP, and all older stack frames.
`entries` identifies the compilation context, not a source-level cost table. -/
def StatementRun (n heapLimit : Nat) (code : Code) (_entries : Nat → Nat)
    (stmt : Stmt) (sourceFinal : Source.State w) (start : State w) : Prop :=
  ∃ steps finish, Exec code steps start finish ∧
    Source.State.Matches heapLimit n sourceFinal finish ∧
    FramePreserved n heapLimit start finish ∧
    finish.pc = start.pc + stmtSize n stmt

def Simulation (n heapLimit : Nat) (code : Code) (entries : Nat → Nat)
    (depth : Nat) (stmt : Stmt) (s s' : Source.State w) : Prop :=
  ∀ t, Source.State.Matches heapLimit n s t →
    heapLimit ≤ (t.regs (ABI.sp n)).toNat → StackFits n depth t →
    CodeAt code t.pc (compileStmt n entries stmt t.pc) →
    StatementRun n heapLimit code entries stmt s' t

/-- The separate call proof must provide this premise for the given depth.
It is not an axiom, a cost annotation, or a claimed completed call theorem. -/
def CallsSimulate (n heapLimit : Nat) (code : Code) (entries : Nat → Nat)
    (depth : Nat) (program : Program) {w : Nat} : Prop :=
  ∀ dst fn args (s s' : Source.State w),
    Source.SafeExec program heapLimit depth (.call dst fn args) s s' →
    (Stmt.call dst fn args).WellFormed n →
    Simulation n heapLimit code entries depth (.call dst fn args) s s'

theorem StackFits.of_frame {n heapLimit depth : Nat} {s t : State w}
    (h : StackFits n depth s) (hf : FramePreserved n heapLimit s t) :
    StackFits n depth t := by
  simpa only [StackFits, hf.sp] using h

private theorem heap_lower_of_frame {n heapLimit : Nat} {s t : State w}
    (h : heapLimit ≤ (s.regs (ABI.sp n)).toNat)
    (hf : FramePreserved n heapLimit s t) :
    heapLimit ≤ (t.regs (ABI.sp n)).toNat := by
  simpa only [hf.sp] using h

@[simp] theorem stmtSize_skip (n : Nat) : stmtSize n .skip = 0 := rfl

@[simp] theorem stmtSize_seq (n : Nat) (a b : Stmt) :
    stmtSize n (.seq a b) = stmtSize n a + stmtSize n b := by
  rw [← compileStmt_length n (fun _ => 0) (.seq a b) 0]
  simp only [compileStmt, List.length_append, compileStmt_length]

@[simp] theorem stmtSize_ite (n : Nat) (c : Expr) (yes no : Stmt) :
    stmtSize n (.ite c yes no) =
      (c.compile (ABI.scratch n)).length + stmtSize n yes + stmtSize n no + 2 := by
  rw [← compileStmt_length n (fun _ => 0) (.ite c yes no) 0]
  simp only [compileStmt, ifCode_length, compileStmt_length]

@[simp] theorem stmtSize_while (n : Nat) (c : Expr) (body : Stmt) :
    stmtSize n (.while c body) =
      (c.compile (ABI.scratch n)).length + stmtSize n body + 2 := by
  rw [← compileStmt_length n (fun _ => 0) (.while c body) 0]
  simp only [compileStmt, whileCode_length, compileStmt_length]

private theorem scratch_bound (n : Nat) : n ≤ ABI.scratch n := by
  simp only [ABI.scratch]
  omega

private theorem sp_scratch (n : Nat) : ABI.sp n < ABI.scratch n := by
  change n < 2 * n + 5
  omega

theorem simulation_skip {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} :
    Simulation n heapLimit code entries depth .skip s s := by
  intro t hm _ _ _
  exact ⟨0, t, .refl t, hm, FramePreserved.refl n heapLimit t, by simp⟩

theorem simulation_assign {n heapLimit depth dst : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.assign dst value).WellFormed n)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    Simulation n heapLimit code entries depth (.assign dst value) s
      (s.setReg dst (s.eval value)) := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.assign hm hwf.1 hwf.2 hr hc
  refine ⟨_, u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.assign dst value) t.pc]
  exact hp

theorem simulation_store {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {address value : Expr}
    (hwf : (Stmt.store address value).WellFormed n)
    (ha : address.ReadsBelow heapLimit s.regs s.mem)
    (hv : value.ReadsBelow heapLimit s.regs s.mem)
    (hd : (s.eval address).toNat < heapLimit) :
    Simulation n heapLimit code entries depth (.store address value) s
      (s.setMem (s.eval address) (s.eval value)) := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.store hm hwf.1 hwf.2 ha hv hd hc
  refine ⟨_, u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.store address value) t.pc]
  exact hp

theorem simulation_read {n heapLimit depth dst : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Word w}
    {rest : List (Word w)} (hwf : (Stmt.read dst).WellFormed n)
    (hi : s.input = value :: rest) :
    Simulation n heapLimit code entries depth (.read dst) s
      { s.setReg dst value with input := rest } := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.read hm hwf value rest hi hc.head
  exact ⟨1, u, he, hu, hf, hp⟩

theorem simulation_write {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {s : Source.State w} {value : Expr}
    (hwf : (Stmt.write value).WellFormed n)
    (hr : value.ReadsBelow heapLimit s.regs s.mem) :
    Simulation n heapLimit code entries depth (.write value) s
      { s with outputRev := s.eval value :: s.outputRev } := by
  intro t hm _ _ hc
  obtain ⟨u, he, hu, hf, hp⟩ := Atomic.write hm hwf hr hc
  refine ⟨_, u, he, hu, hf, ?_⟩
  rw [← compileStmt_length n entries (.write value) t.pc]
  exact hp

theorem simulation_seq {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {a b : Stmt} {s middle s' : Source.State w}
    (first : Simulation n heapLimit code entries depth a s middle)
    (second : Simulation n heapLimit code entries depth b middle s') :
    Simulation n heapLimit code entries depth (.seq a b) s s' := by
  intro t hm hlo hfit hc
  change CodeAt code t.pc (compileStmt n entries a t.pc ++
    compileStmt n entries b (t.pc + (compileStmt n entries a t.pc).length)) at hc
  obtain ⟨na, u, hea, hmu, hfa, hpa⟩ := first t hm hlo hfit hc.append_left
  have hcb : CodeAt code u.pc (compileStmt n entries b u.pc) := by
    rw [hpa]
    simpa only [compileStmt_length] using hc.append_right
  obtain ⟨nb, v, heb, hmv, hfb, hpb⟩ := second u hmu
    (heap_lower_of_frame hlo hfa) (hfit.of_frame hfa) hcb
  refine ⟨na + nb, v, hea.trans heb, hmv, hfa.trans hfb, ?_⟩
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

theorem simulation_iteTrue {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {yes no : Stmt} {s s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (body : Simulation n heapLimit code entries depth yes s s') :
    Simulation n heapLimit code entries depth (.ite c yes no) s s' := by
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
  obtain ⟨nb, u, heb, hmu, hfu, hpu⟩ := body g.next hmg.next
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
  refine ⟨condCode.length + 1 + nb + 1, u.atPC target,
    Ram.ifCode_then hc (Expr.compile_linear c _) hm.running hzg heb hp hmu.running,
    hmu.atPC target, (hfb.trans hfu).trans (FramePreserved.atPC n heapLimit u target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_ite]
  simp only [yesCode, noCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_iteFalse {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {yes no : Stmt} {s s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0)
    (body : Simulation n heapLimit code entries depth no s s') :
    Simulation n heapLimit code entries depth (.ite c yes no) s s' := by
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
  obtain ⟨nb, u, heb, hmu, hfu, hpu⟩ := body (g.atPC noStart) (hmg.atPC noStart)
    (heap_lower_of_frame hlo hfb) (hfit.of_frame hfb) hcb
  have hzg : g.regs (ABI.scratch n) = 0 := hvg.trans hz
  refine ⟨condCode.length + 1 + nb, u,
    Ram.ifCode_else hc (Expr.compile_linear c _) hm.running hzg heb,
    hmu, hfb.trans hfu, ?_⟩
  simp only [State.atPC_pc, noStart, yesCode, compileStmt_length, condCode] at hpu
  rw [stmtSize_ite]
  omega

theorem simulation_whileFalse {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {body : Stmt} {s : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c = 0) :
    Simulation n heapLimit code entries depth (.while c body) s s := by
  intro t hm _ _ hc
  let condCode := c.compile (ABI.scratch n)
  let bodyCode := compileStmt n entries body (t.pc + condCode.length + 1)
  let g := execBlock condCode t
  let target := t.pc + condCode.length + bodyCode.length + 2
  change CodeAt code t.pc (whileCode condCode (ABI.scratch n) bodyCode t.pc) at hc
  obtain ⟨hmg, hfg, hvg, _⟩ := guard_properties hm hb hr
  have hzg : g.regs (ABI.scratch n) = 0 := hvg.trans hz
  refine ⟨condCode.length + 1, g.atPC target,
    Ram.whileCode_exit hc (Expr.compile_linear c _) hm.running hzg,
    hmg.atPC target, hfg.trans (FramePreserved.atPC n heapLimit g target), ?_⟩
  simp only [State.atPC_pc, target, stmtSize_while]
  simp only [bodyCode, compileStmt_length, condCode, Nat.add_assoc]

theorem simulation_whileTrue {n heapLimit depth : Nat} {code : Code}
    {entries : Nat → Nat} {c : Expr} {body : Stmt} {s middle s' : Source.State w}
    (hb : c.Bounded n) (hr : c.ReadsBelow heapLimit s.regs s.mem)
    (hz : s.eval c ≠ 0)
    (iteration : Simulation n heapLimit code entries depth body s middle)
    (rest : Simulation n heapLimit code entries depth (.while c body) middle s') :
    Simulation n heapLimit code entries depth (.while c body) s s' := by
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
  obtain ⟨nb, u, heb, hmu, hfu, hpu⟩ := iteration g.next hmg.next
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
  obtain ⟨nr, v, her, hmv, hfv, hpv⟩ := rest (u.atPC t.pc) (hmu.atPC t.pc)
    (heap_lower_of_frame hlo hfi) (hfit.of_frame hfi) hc
  exact ⟨_, v, hi.trans her, hmv, hfi.trans hfv, hpv⟩

/-- All structured forms simulate once the separate call theorem is supplied.
The call case deliberately uses `hcalls`, not an unproved machine transition. -/
theorem simulate {n heapLimit depth : Nat} {code : Code} {entries : Nat → Nat}
    {program : Program} {stmt : Stmt} {s s' : Source.State w}
    (hx : Source.SafeExec program heapLimit depth stmt s s')
    (hwf : stmt.WellFormed n)
    (hcalls : CallsSimulate n heapLimit code entries depth program (w := w)) :
    Simulation n heapLimit code entries depth stmt s s' := by
  induction hx with
  | skip => exact simulation_skip
  | assign reads => exact simulation_assign hwf reads
  | store addressReads valueReads destination =>
      exact simulation_store hwf addressReads valueReads destination
  | seq _ _ first second =>
      exact simulation_seq (first hwf.1 hcalls) (second hwf.2 hcalls)
  | iteTrue reads condition _ body =>
      exact simulation_iteTrue hwf.1 reads condition (body hwf.2.1 hcalls)
  | iteFalse reads condition _ body =>
      exact simulation_iteFalse hwf.1 reads condition (body hwf.2.2 hcalls)
  | whileFalse reads condition => exact simulation_whileFalse hwf.1 reads condition
  | whileTrue reads condition _ _ body rest =>
      exact simulation_whileTrue hwf.1 reads condition (body hwf.2 hcalls) (rest hwf hcalls)
  | read available => exact simulation_read hwf available
  | write reads => exact simulation_write hwf reads
  | call lookup arity resultCount frame arguments body results _ =>
      exact hcalls _ _ _ _ _ (.call lookup arity resultCount frame arguments body results) hwf

end Compiler
end Ram
