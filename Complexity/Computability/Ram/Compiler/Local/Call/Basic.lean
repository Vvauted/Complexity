/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Results.Receive
import Complexity.Computability.Ram.Compiler.Local.Basic
import Complexity.Computability.Ram.Compiler.Local.Call.Return
import Complexity.Computability.Ram.Compiler.Local.Call.Setup
import Complexity.Computability.Ram.Compiler.Local.Exact.Basic

/-!
# Complete calls with callee-sized frames

The concrete setup, body, return, and receive segments compose into one exact
RAM execution. The caller and callee may have different local-register bounds.
Registers above the callee's bound survive its body, while lower registers are
restored from the saved frame. Thus the call restores every caller register
outside its ordered result destinations, including through nested larger callees.
-/

namespace Ram.LocalCompiler

/-- Split a concrete call into setup, jump and receiver. The receiver may be
empty; the call's continuation does not require a dummy result instruction. -/
theorem callCodeResults_layout {code : Code} {control locals entry base : Nat}
    {dsts : List Reg} {args : List Expr}
    (h : CodeAt code base (ABI.callCodeResultsLocals control locals entry dsts args base)) :
    CodeAt code base (ABI.callPrefixLocals control locals args
        (base + (ABI.callPrefixLocals control locals args 0).length + 1)) ∧
      code[base + (ABI.callPrefixLocals control locals args 0).length]? = some (.jump entry) ∧
      CodeAt code (base + (ABI.callPrefixLocals control locals args 0).length + 1)
        (ABI.receiveResults control 0 dsts) := by
  change CodeAt code base
    (ABI.callPrefixLocals control locals args _ ++
      .jump entry :: ABI.receiveResults control 0 dsts) at h
  have ht := h.append_right
  refine ⟨h.append_left, ?_, ?_⟩
  · simpa only [ABI.callPrefixLocals_length control locals args _ 0] using ht.head
  · simpa only [ABI.callPrefixLocals_length control locals args _ 0] using ht.tail

structure CallLayout (code : Code) (control locals entry : Nat) (dsts : List Reg)
    (args : List Expr) (base : Nat) : Prop where
  setup : CodeAt code base
    (ABI.callPrefixLocals control locals args
      (base + (ABI.callPrefixLocals control locals args 0).length + 1))
  jump : code[base + (ABI.callPrefixLocals control locals args 0).length]? =
    some (.jump entry)
  receive : CodeAt code (base + (ABI.callPrefixLocals control locals args 0).length + 1)
    (ABI.receiveResults control 0 dsts)

theorem callCode_layout {code : Code} {control locals entry base : Nat}
    {dsts : List Reg} {args : List Expr}
    (h : CodeAt code base (ABI.callCodeResultsLocals control locals entry dsts args base)) :
    CallLayout code control locals entry dsts args base := by
  obtain ⟨setup, jump, receive⟩ := callCodeResults_layout h
  exact ⟨setup, jump, receive⟩

/-- The cost is the sum of actual instruction-segment counts. In particular,
saving and restoring the callee's locals is not a bulk or annotated operation. -/
theorem simulate_call_exact
    {control caller heapLimit depth fn bodySteps : Nat}
    {dsts : List Reg} {args : List Expr} {code : Code} {localsTable entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hcaller : caller ≤ control)
    (hlocals : f.locals ≤ control)
    (htable : localsTable fn = f.locals)
    (hdsts : ∀ dst ∈ dsts, dst < caller)
    (hargs : ∀ a ∈ args, a.Bounded caller)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ f.locals)
    (hresultCount : dsts.length = f.results.length)
    (hresultCapacity : f.results.length - 1 ≤ control)
    (hresults : ∀ e ∈ f.results, e.Bounded f.locals)
    (hresultReads : ∀ e ∈ f.results, e.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc control localsTable entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : SimulationExact control f.locals heapLimit code localsTable entries depth
      f.body bodySteps (s.enter (args.map s.eval)) callee) :
    SimulationExact control caller heapLimit code localsTable entries (depth + 1)
      (.call dsts fn args)
      ((ABI.callPrefixLocals control f.locals args 0).length + 1 + bodySteps +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length)
      s (s.leave callee dsts f.results) := by
  intro _ t hm hheap hfit hcode
  change CodeAt code t.pc
    (ABI.callCodeResultsLocals control (localsTable fn) (entries fn) dsts args t.pc) at hcode
  rw [htable] at hcode
  have hl := callCode_layout hcode
  let returnPC := t.pc + (ABI.callPrefixLocals control f.locals args 0).length + 1
  let prepared := execBlock (ABI.callPrefixLocals control f.locals args returnPC) t
  let entered := prepared.atPC (entries fn)
  have hframeFit : (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals < 2 ^ w := by
    change (t.regs (ABI.sp control)).toNat +
      (depth + 1) * ABI.frameSize control < 2 ^ w at hfit
    rw [Nat.add_mul, Nat.one_mul] at hfit
    simp only [ABI.frameSize] at hfit ⊢
    omega
  have hp : ABI.CallPreparedLocals control f.locals heapLimit args returnPC s t prepared :=
    ABI.callPrefixLocals_correct hm hcaller hlocals hargs hreads hcount hheap hframeFit
  have hprefix : Exec code (ABI.callPrefixLocals control f.locals args returnPC).length
      t prepared := ABI.callPrefixLocals_exec hl.setup hm.running
  have hjump : Exec code 1 prepared entered := by
    apply Exec.jump hp.matched.running
    rw [hp.pc, ABI.callPrefixLocals_length control f.locals args returnPC 0]
    exact hl.jump
  have henteredSP : (entered.regs (ABI.sp control)).toNat =
      (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals := hp.sp
  have hchildHeap : heapLimit ≤ (entered.regs (ABI.sp control)).toNat := by
    rw [henteredSP]
    omega
  have hchildFit : Compiler.StackFits control depth entered := by
    change (entered.regs (ABI.sp control)).toNat + depth * ABI.frameSize control < 2 ^ w
    rw [henteredSP]
    change (t.regs (ABI.sp control)).toNat +
      (depth + 1) * ABI.frameSize control < 2 ^ w at hfit
    rw [Nat.add_mul, Nat.one_mul] at hfit
    simp only [ABI.frameSize] at hfit ⊢
    omega
  change CodeAt code (entries fn)
    (compileStmt control localsTable entries f.body (entries fn) ++
      ABI.returnCodeResultsLocals control f.locals f.results) at hfunction
  have hbodyAt : CodeAt code entered.pc
      (compileStmt control localsTable entries f.body entered.pc) := hfunction.append_left
  obtain ⟨q, hbodyExec, hcallee, hbodyFrame, hbodyRegs, hbodyPC⟩ :=
    hbody hlocals entered (hp.matched.atPC (entries fn)) hchildHeap hchildFit hbodyAt
  have hqSP : (q.regs (ABI.sp control)).toNat =
      (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals := by
    rw [hbodyFrame.sp]
    exact henteredSP
  have hheader : q.mem (t.regs (ABI.sp control)) = BitVec.ofNat w returnPC := by
    have hbelow : (t.regs (ABI.sp control)).toNat < (entered.regs (ABI.sp control)).toNat := by
      rw [henteredSP]
      simp [ABI.frameSize]
    rw [hbodyFrame.older (t.regs (ABI.sp control)) hheap hbelow]
    exact hp.returnAddress
  have hsaved : ABI.FrameSaved f.locals (t.regs (ABI.sp control)) t.regs q.mem :=
    hbodyFrame.frameSaved hheap (Nat.le_of_eq henteredSP.symm) hp.saved
  have hreturnAt : CodeAt code q.pc
      (ABI.returnCodeResultsLocals control f.locals f.results) := by
    rw [hbodyPC]
    simpa only [entered, State.atPC_pc, compileStmt_length] using hfunction.append_right
  have hr := ABI.returnPrefixResultsLocals_correct hlocals hcallee hresultCapacity
    hresults hresultReads hframeFit hqSP hsaved hheader
  let restored := execBlock (ABI.returnPrefixResultsLocals control f.locals f.results) q
  let back := restored.atPC returnPC
  let finish := execBlock (ABI.receiveResults control 0 dsts) back
  have hreturnFit : returnPC < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hl.jump).1) hcodefit
  have hreturnExec : Exec code
      (ABI.returnCodeResultsLocals control f.locals f.results).length q back :=
    ABI.returnCodeResultsLocals_exec hr hreturnAt hcallee.running
      (Word.ofNat_toNat_of_lt hreturnFit)
  have hreceive : Exec code dsts.length back finish :=
    ABI.receiveResults_exec hl.receive (hr.status.trans hcallee.running)
  have hfull := (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec).trans hreceive
  have hrestored : ∀ r, r < control → restored.regs r = t.regs r := by
    intro r hrN
    by_cases hrl : r < f.locals
    · exact hr.locals r hrl
    · have hrl' := Nat.le_of_not_gt hrl
      exact (hr.preservedAbove r hrl' hrN).trans
        ((hbodyRegs r hrl' hrN).trans (hp.above r hrl' hrN))
  have hmatched : ({ callee with regs := s.regs } : Source.State w).Matches
      heapLimit caller back := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hrCaller
      exact (hm.regs r hrCaller).trans
        (hrestored r (Nat.lt_of_lt_of_le hrCaller hcaller)).symm
    · intro a ha
      change callee.mem a = restored.mem a
      rw [hr.memory]
      exact hcallee.heap a ha
    · change callee.input = restored.input
      exact hcallee.input.trans hr.input.symm
    · change callee.outputRev = restored.outputRev
      exact hcallee.output.trans hr.output.symm
    · exact hr.status.trans hcallee.running
  have hreceived := ABI.receiveResults_correct (start := 0)
    (fun dst hd => Nat.lt_of_lt_of_le (hdsts dst hd) hcaller) back
  refine ⟨finish, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ABI.callPrefixLocals_length control f.locals args returnPC 0] using hfull
  · apply ABI.receiveResults_matches hmatched hcaller hdsts
    · simpa only [List.length_map] using hresultCount
    · intro i hi
      simpa only [List.length_map, List.getElem_map, Nat.zero_add] using
        hr.values i (by simpa only [List.length_map] using hi)
  · refine ⟨?_, ?_⟩
    · exact (hreceived.preserved (ABI.sp control) (by
        intro hmem
        have hlt : control < caller := hdsts _ hmem
        omega)).trans hr.sp
    · intro a ha hb
      change finish.mem a = t.mem a
      rw [hreceived.memory]
      change restored.mem a = t.mem a
      rw [hr.memory]
      have hb' : a.toNat < (entered.regs (ABI.sp control)).toNat := by
        rw [henteredSP]
        omega
      exact (hbodyFrame.older a ha hb').trans (hp.below a hb)
  · intro r hrCaller hrN
    exact (hreceived.preserved r (by
      intro hmem
      exact Nat.not_lt_of_ge hrCaller (hdsts r hmem))).trans (hrestored r hrN)
  · change finish.pc = t.pc + stmtSize control localsTable (.call dsts fn args)
    rw [ABI.receiveResults_pc]
    change returnPC + dsts.length = t.pc + stmtSize control localsTable (.call dsts fn args)
    rw [stmtSize_call, htable]
    simp only [returnPC, Nat.add_assoc]

end Ram.LocalCompiler
