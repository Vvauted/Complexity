/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Compiler
import Ram.CallSetup
import Ram.CallReturn
import Ram.Structural
import Ram.Exact
import Ram.CodeLength

/-!
# Calls through the concrete ABI

Call setup, body execution, return, and the receive instruction are all actual
RAM execution segments. The body simulation is the induction premise supplied
by the smaller call-depth theorem, including for self and mutual recursion.
-/

namespace Ram.Compiler

structure CallLayout (code : Code) (n entry dst : Nat) (args : List Expr)
    (base : Nat) : Prop where
  setup : CodeAt code base
    (ABI.callPrefix n args (base + (ABI.callPrefix n args 0).length + 1))
  jump : code[base + (ABI.callPrefix n args 0).length]? = some (.jump entry)
  receive : code[base + (ABI.callPrefix n args 0).length + 1]? = some (.move dst (ABI.rv n))

theorem callCode_layout {code : Code} {n entry dst base : Nat} {args : List Expr}
    (h : CodeAt code base (ABI.callCode n entry dst args base)) :
    CallLayout code n entry dst args base := by
  change CodeAt code base (ABI.callPrefix n args _ ++ [.jump entry, .move dst (ABI.rv n)]) at h
  have ht := h.append_right
  refine ⟨h.append_left, ?_, ?_⟩
  · simpa only [ABI.callPrefix_length n args _ 0] using ht.head
  · simpa only [ABI.callPrefix_length n args _ 0] using ht.tail.head

/-- A fetched instruction's address lies in the actual code list. -/
theorem pc_lt_length_of_fetch {code : Code} {pc : Nat} {i : Instr}
    (h : code[pc]? = some i) : pc < code.length :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem call_run
    {n heapLimit depth dst fn : Nat}
    {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    {accept : Nat → Prop}
    (hdst : dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresult : f.result.Bounded n)
    (hresultReads : f.result.ReadsBelow heapLimit callee.regs callee.mem)
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
      CodeAt code t.pc (compileStmt n entries (.call dst fn args) t.pc) →
      ∃ bodySteps, accept bodySteps ∧
        StatementRunExact n heapLimit code entries (.call dst fn args)
          ((ABI.callPrefix n args 0).length + 1 + bodySteps +
            (ABI.returnCode n f.result).length + 1)
          (s.leave callee dst f.result) t := by
  intro t hm hheap hfit hcode
  change CodeAt code t.pc (ABI.callCode n (entries fn) dst args t.pc) at hcode
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
    (compileStmt n entries f.body (entries fn) ++ ABI.returnCode n f.result) at hfunction
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
  have hsaved : ABI.FrameSaved n (t.regs (ABI.sp n)) t.regs q.mem := by
    intro i hi
    have hslotFit : (t.regs (ABI.sp n)).toNat + (i + 1) < 2 ^ w := by
      change (t.regs (ABI.sp n)).toNat + (n + 1) < 2 ^ w at hframeFit
      omega
    have ha := arrayAddr_toNat hslotFit
    have hlo : heapLimit ≤ (arrayAddr (t.regs (ABI.sp n)) (i + 1)).toNat := by
      rw [ha]
      omega
    have hhi : (arrayAddr (t.regs (ABI.sp n)) (i + 1)).toNat <
        (entered.regs (ABI.sp n)).toNat := by
      rw [ha, henteredSP]
      simp only [ABI.frameSize]
      omega
    rw [hbodyFrame.older _ hlo hhi]
    exact hp.saved i hi
  have hreturnAt : CodeAt code q.pc (ABI.returnCode n f.result) := by
    rw [hbodyPC]
    simpa only [entered, State.atPC_pc, compileStmt_length] using hfunction.append_right
  have hr := ABI.returnPrefix_correct hcallee hresult hresultReads hframeFit hqSP hsaved hheader
  let restored := execBlock (ABI.returnPrefix n f.result) q
  let back := restored.atPC returnPC
  let finish := execInstr (.move dst (ABI.rv n)) back
  have hreturnFit : returnPC < 2 ^ w :=
    Nat.lt_trans (pc_lt_length_of_fetch hl.receive) hcodefit
  have hreturnExec : Exec code (ABI.returnCode n f.result).length q back :=
    ABI.returnCode_exec hr hreturnAt hcallee.running (Word.ofNat_toNat_of_lt hreturnFit)
  have hreceive : Exec code 1 back finish :=
    Exec.single (step_of_fetch (hr.status.trans hcallee.running) hl.receive)
  have hfull := (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec).trans hreceive
  refine ⟨bodySteps, haccept, finish, ?_, ?_, ?_, ?_⟩
  · simpa only [ABI.callPrefix_length n args returnPC 0] using hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hrn
      change (if r = dst then callee.eval f.result else s.regs r) =
        (if r = dst then restored.regs (ABI.rv n) else restored.regs r)
      by_cases heq : r = dst
      · simp only [if_pos heq]
        exact hr.value.symm
      · simp only [if_neg heq]
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
  · refine ⟨?_, ?_⟩
    · change (back.setReg dst (back.regs (ABI.rv n))).regs (ABI.sp n) = t.regs (ABI.sp n)
      have hne : ABI.sp n ≠ dst := Ne.symm (Nat.ne_of_lt hdst)
      exact (State.setReg_ne back dst (ABI.sp n) (back.regs (ABI.rv n)) hne).trans hr.sp
    · intro a ha hb
      change restored.mem a = t.mem a
      rw [hr.memory]
      have hb' : a.toNat < (entered.regs (ABI.sp n)).toNat := by
        rw [henteredSP]
        omega
      exact (hbodyFrame.older a ha hb').trans (hp.below a hb)
  · change returnPC + 1 = t.pc + stmtSize n (.call dst fn args)
    rw [← compileStmt_length n entries (.call dst fn args) t.pc]
    simp only [compileStmt, ABI.callCode_length, returnPC, Nat.add_assoc]

/-- A call saves its actual frame, runs the body, restores the frame, and
receives the result. The smaller-depth body simulation is an induction premise,
not an assumed implementation of a recursive call. -/
theorem simulate_call
    {n heapLimit depth dst fn : Nat}
    {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hdst : dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresult : f.result.Bounded n)
    (hresultReads : f.result.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc n entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : Simulation n heapLimit code entries depth f.body
      (s.enter (args.map s.eval)) callee) :
    Simulation n heapLimit code entries (depth + 1)
      (.call dst fn args) s (s.leave callee dst f.result) := by
  intro t hm hheap hfit hcode
  obtain ⟨_, _, hrun⟩ := call_run (accept := fun _ => True)
    hdst hargs hreads hcount hresult hresultReads hfunction hcodefit
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
    {n heapLimit depth dst fn bodySteps : Nat}
    {args : List Expr} {code : Code} {entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hdst : dst < n)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ n)
    (hresult : f.result.Bounded n)
    (hresultReads : f.result.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc n entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : SimulationExact n heapLimit code entries depth f.body bodySteps
      (s.enter (args.map s.eval)) callee) :
    SimulationExact n heapLimit code entries (depth + 1) (.call dst fn args)
      ((ABI.callPrefix n args 0).length + 1 + bodySteps +
        (ABI.returnCode n f.result).length + 1)
      s (s.leave callee dst f.result) := by
  intro t hm hheap hfit hcode
  obtain ⟨steps, hsteps, hrun⟩ := call_run (accept := fun steps => steps = bodySteps)
    hdst hargs hreads hcount hresult hresultReads hfunction hcodefit
    (by
      intro u hu hlo hspace hat
      exact ⟨bodySteps, rfl, hbody u hu hlo hspace hat⟩)
    t hm hheap hfit hcode
  simpa only [hsteps] using hrun

end Ram.Compiler
