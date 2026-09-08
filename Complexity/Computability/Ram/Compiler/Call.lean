/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.CallReturn
import Complexity.Computability.Ram.Compiler.ABI.CallSetup
import Complexity.Computability.Ram.Compiler.ABI.CodeLength
import Complexity.Computability.Ram.Compiler.ABI.Results.Receive
import Complexity.Computability.Ram.Compiler.Basic
import Complexity.Computability.Ram.Compiler.Exact
import Complexity.Computability.Ram.Compiler.Simulation

/-!
# Calls through the concrete ABI

Call setup, body execution, return, and the receive instructions are all actual
RAM execution segments. The body simulation is the induction premise supplied
by the smaller call-depth theorem, including for self and mutual recursion.
-/

namespace Ram.Compiler

structure CallLayout (code : Code) (n entry : Nat) (dsts : List Reg) (args : List Expr)
    (base : Nat) : Prop where
  setup : CodeAt code base
    (ABI.callPrefix n args (base + (ABI.callPrefix n args 0).length + 1))
  jump : code[base + (ABI.callPrefix n args 0).length]? = some (.jump entry)
  receive : CodeAt code (base + (ABI.callPrefix n args 0).length + 1)
    (ABI.receiveResults n 0 dsts)

theorem callCode_layout {code : Code} {n entry base : Nat}
    {dsts : List Reg} {args : List Expr}
    (h : CodeAt code base (ABI.callCodeResults n entry dsts args base)) :
    CallLayout code n entry dsts args base := by
  change CodeAt code base
    (ABI.callPrefix n args _ ++ .jump entry :: ABI.receiveResults n 0 dsts) at h
  have ht := h.append_right
  refine ⟨h.append_left, ?_, ?_⟩
  · simpa only [ABI.callPrefix_length n args _ 0] using ht.head
  · simpa only [ABI.callPrefix_length n args _ 0] using ht.tail

/-- A fetched instruction's address lies in the actual code list. -/
theorem pc_lt_length_of_fetch {code : Code} {pc : Nat} {i : Instr}
    (h : code[pc]? = some i) : pc < code.length :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem call_run
    {n heapLimit depth fn : Nat}
    {dsts : List Reg} {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    {accept : Nat → Prop}
    (hdsts : ∀ dst ∈ dsts, dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresultCount : dsts.length = f.results.length)
    (hresultCapacity : f.results.length - 1 ≤ n)
    (hresults : ∀ e ∈ f.results, e.Bounded n)
    (hresultReads : ∀ e ∈ f.results, e.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc n entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : ∀ u, (s.enter (args.map s.eval)).Matches heapLimit n u →
      heapLimit ≤ (u.regs (ABI.sp n)).toNat → StackFits n depth u →
      CodeAt code u.pc (compileStmt n entries f.body u.pc) →
      ∃ bodySteps, accept bodySteps ∧
        StatementRunExact n heapLimit code entries f.body bodySteps callee u) :
    ∀ t, s.Matches heapLimit n t →
      heapLimit ≤ (t.regs (ABI.sp n)).toNat → StackFits n (depth + 1) t →
      CodeAt code t.pc (compileStmt n entries (.call dsts fn args) t.pc) →
      ∃ bodySteps, accept bodySteps ∧
        StatementRunExact n heapLimit code entries (.call dsts fn args)
          ((ABI.callPrefix n args 0).length + 1 + bodySteps +
            (ABI.returnCodeResults n f.results).length + dsts.length)
          (s.leave callee dsts f.results) t := by
  intro t hm hheap hfit hcode
  change CodeAt code t.pc (ABI.callCodeResults n (entries fn) dsts args t.pc) at hcode
  have hl := callCode_layout hcode
  let returnPC := t.pc + (ABI.callPrefix n args 0).length + 1
  let prepared := execBlock (ABI.callPrefix n args returnPC) t
  let entered := prepared.atPC (entries fn)
  have hframeFit : (t.regs (ABI.sp n)).toNat + ABI.frameSize n < 2 ^ w := by
    change (t.regs (ABI.sp n)).toNat + (depth + 1) * ABI.frameSize n < 2 ^ w at hfit
    rw [Nat.add_mul, Nat.one_mul] at hfit
    omega
  have hp : ABI.CallPrepared n heapLimit args returnPC s t prepared :=
    ABI.callPrefix_correct hm hargs hreads hcount hheap hframeFit
  have hprefix : Exec code (ABI.callPrefix n args returnPC).length t prepared :=
    ABI.callPrefix_exec hl.setup hm.running
  have hjump : Exec code 1 prepared entered := by
    apply Exec.jump hp.matched.running
    rw [hp.pc, ABI.callPrefix_length n args returnPC 0]
    exact hl.jump
  have henteredSP : (entered.regs (ABI.sp n)).toNat =
      (t.regs (ABI.sp n)).toNat + ABI.frameSize n := hp.sp
  have hchildHeap : heapLimit ≤ (entered.regs (ABI.sp n)).toNat := by
    rw [henteredSP]
    omega
  have hchildFit : StackFits n depth entered := by
    change (entered.regs (ABI.sp n)).toNat + depth * ABI.frameSize n < 2 ^ w
    rw [henteredSP]
    change (t.regs (ABI.sp n)).toNat + (depth + 1) * ABI.frameSize n < 2 ^ w at hfit
    rw [Nat.add_mul, Nat.one_mul] at hfit
    omega
  change CodeAt code (entries fn)
    (compileStmt n entries f.body (entries fn) ++ ABI.returnCodeResults n f.results) at hfunction
  have hbodyAt : CodeAt code entered.pc (compileStmt n entries f.body entered.pc) :=
    hfunction.append_left
  obtain ⟨bodySteps, haccept, q, hbodyExec, hcallee, hbodyFrame, hbodyPC⟩ :=
    hbody entered (hp.matched.atPC (entries fn)) hchildHeap hchildFit hbodyAt
  have hqSP : (q.regs (ABI.sp n)).toNat =
      (t.regs (ABI.sp n)).toNat + ABI.frameSize n := by
    rw [hbodyFrame.sp]
    exact henteredSP
  have hheader : q.mem (t.regs (ABI.sp n)) = BitVec.ofNat w returnPC := by
    rw [hbodyFrame.older (t.regs (ABI.sp n)) hheap (by
      rw [henteredSP]
      simp [ABI.frameSize])]
    exact hp.returnAddress
  have hsaved : ABI.FrameSaved n (t.regs (ABI.sp n)) t.regs q.mem :=
    hbodyFrame.frameSaved hheap (Nat.le_of_eq henteredSP.symm) hp.saved
  have hreturnAt : CodeAt code q.pc (ABI.returnCodeResults n f.results) := by
    rw [hbodyPC]
    simpa only [entered, State.atPC_pc, compileStmt_length] using hfunction.append_right
  have hr := ABI.returnPrefixResults_correct hcallee hresultCapacity hresults hresultReads
    hframeFit hqSP hsaved hheader
  let restored := execBlock (ABI.returnPrefixResults n f.results) q
  let back := restored.atPC returnPC
  let finish := execBlock (ABI.receiveResults n 0 dsts) back
  have hreturnFit : returnPC < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (pc_lt_length_of_fetch hl.jump)) hcodefit
  have hreturnExec : Exec code (ABI.returnCodeResults n f.results).length q back :=
    ABI.returnCodeResults_exec hr hreturnAt hcallee.running (Word.ofNat_toNat_of_lt hreturnFit)
  have hreceive : Exec code dsts.length back finish :=
    ABI.receiveResults_exec hl.receive (hr.status.trans hcallee.running)
  have hfull := (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec).trans hreceive
  have hmatched : ({ callee with regs := s.regs } : Source.State w).Matches
      heapLimit n back := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hrn
      exact (hm.regs r hrn).trans (hr.locals r hrn).symm
    · intro a ha
      change callee.mem a = restored.mem a
      rw [hr.memory]
      exact hcallee.heap a ha
    · change callee.input = restored.input
      exact hcallee.input.trans hr.input.symm
    · change callee.outputRev = restored.outputRev
      exact hcallee.output.trans hr.output.symm
    · exact hr.status.trans hcallee.running
  have hreceived := ABI.receiveResults_correct (start := 0) hdsts back
  refine ⟨bodySteps, haccept, finish, ?_, ?_, ?_, ?_⟩
  · simpa only [ABI.callPrefix_length n args returnPC 0] using hfull
  · apply ABI.receiveResults_matches hmatched (Nat.le_refl n) hdsts
    · simpa only [List.length_map] using hresultCount
    · intro i hi
      simpa only [List.length_map, List.getElem_map, Nat.zero_add] using
        hr.values i (by simpa only [List.length_map] using hi)
  · refine ⟨?_, ?_⟩
    · exact (hreceived.preserved (ABI.sp n)
        (fun hmem => Nat.lt_irrefl n (hdsts _ hmem))).trans hr.sp
    · intro a ha hb
      change finish.mem a = t.mem a
      rw [hreceived.memory]
      change restored.mem a = t.mem a
      rw [hr.memory]
      have hb' : a.toNat < (entered.regs (ABI.sp n)).toNat := by
        rw [henteredSP]
        omega
      exact (hbodyFrame.older a ha hb').trans (hp.below a hb)
  · change finish.pc = t.pc + stmtSize n (.call dsts fn args)
    rw [ABI.receiveResults_pc]
    change returnPC + dsts.length = t.pc + stmtSize n (.call dsts fn args)
    rw [← compileStmt_length n entries (.call dsts fn args) t.pc]
    simp only [compileStmt, ABI.callCodeResults_length, returnPC, Nat.add_assoc]
    omega

/-- A call saves its actual frame, runs the body, restores the frame, and
receives the ordered results. The smaller-depth body simulation is an induction premise,
not an assumed implementation of a recursive call. -/
theorem simulate_call
    {n heapLimit depth fn : Nat}
    {dsts : List Reg} {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hdsts : ∀ dst ∈ dsts, dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresultCount : dsts.length = f.results.length)
    (hresultCapacity : f.results.length - 1 ≤ n)
    (hresults : ∀ e ∈ f.results, e.Bounded n)
    (hresultReads : ∀ e ∈ f.results, e.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc n entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : Simulation n heapLimit code entries depth f.body
      (s.enter (args.map s.eval)) callee) :
    Simulation n heapLimit code entries (depth + 1)
      (.call dsts fn args) s (s.leave callee dsts f.results) := by
  intro t hm hheap hfit hcode
  obtain ⟨_, _, hrun⟩ := call_run (accept := fun _ => True)
    hdsts hargs hreads hcount hresultCount hresultCapacity hresults hresultReads hfunction hcodefit
    (by
      intro u hu hlo hspace hat
      obtain ⟨steps, finish, he, hs, hf, hp⟩ := hbody u hu hlo hspace hat
      exact ⟨steps, trivial, finish, he, hs, hf, hp⟩)
    t hm hheap hfit hcode
  exact hrun.erase

/-- The call's exact count consists of the emitted setup, entry jump, the
body's actual count, emitted return, and receive. No caller chooses a price for
a call or frame operation. -/
theorem simulate_call_exact
    {n heapLimit depth fn bodySteps : Nat}
    {dsts : List Reg} {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hdsts : ∀ dst ∈ dsts, dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresultCount : dsts.length = f.results.length)
    (hresultCapacity : f.results.length - 1 ≤ n)
    (hresults : ∀ e ∈ f.results, e.Bounded n)
    (hresultReads : ∀ e ∈ f.results, e.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc n entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : SimulationExact n heapLimit code entries depth f.body bodySteps
      (s.enter (args.map s.eval)) callee) :
    SimulationExact n heapLimit code entries (depth + 1) (.call dsts fn args)
      ((ABI.callPrefix n args 0).length + 1 + bodySteps +
        (ABI.returnCodeResults n f.results).length + dsts.length)
      s (s.leave callee dsts f.results) := by
  intro t hm hheap hfit hcode
  obtain ⟨steps, hsteps, hrun⟩ := call_run (accept := fun steps => steps = bodySteps)
    hdsts hargs hreads hcount hresultCount hresultCapacity hresults hresultReads hfunction hcodefit
    (by
      intro u hu hlo hspace hat
      exact ⟨bodySteps, rfl, hbody u hu hlo hspace hat⟩)
    t hm hheap hfit hcode
  simpa only [hsteps] using hrun

end Ram.Compiler
