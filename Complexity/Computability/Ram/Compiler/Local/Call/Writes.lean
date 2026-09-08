/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Call.Basic
import Complexity.Computability.Ram.Compiler.Local.Exact.Frame

/-!
# Actual writes throughout a recursive call

The exact call simulation supplies the setup, jump, body, return and receive
transitions. Their actual write sets are joined at those same execution cuts.
Setup writes exactly the new callee-sized frame, the body writes only its
source heap or its own stack region, and return, jump and receive do not write.

The resulting bound protects older frames throughout execution. The body's
actual no-write bound also preserves the saved values needed for return,
using the general prefix frame-preservation interface.
-/

namespace Ram.LocalCompiler

/-- Complete exact call simulation whose actual writes avoid all older frames.
The body hypothesis retains its real entry SP, and the call's step count is
unchanged from `simulate_call_exact`. -/
theorem simulate_call_writes
    {control caller heapLimit depth dst fn bodySteps : Nat}
    {args : List Expr} {code : Code} {localsTable entries : Nat → Nat}
    {s callee : Source.State w} {f : Func}
    (hcaller : caller ≤ control)
    (hlocals : f.locals ≤ control)
    (htable : localsTable fn = f.locals)
    (hdst : dst < caller)
    (hargs : ∀ a ∈ args, a.Bounded caller)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ f.locals)
    (hresult : f.result.Bounded f.locals)
    (hresultReads : f.result.ReadsBelow heapLimit callee.regs callee.mem)
    (hfunction : CodeAt code (entries fn)
      (compileFunc control localsTable entries f (entries fn)))
    (hcodefit : code.length < 2 ^ w)
    (hbody : SimulationWrites control f.locals heapLimit code localsTable entries depth
      f.body bodySteps (s.enter (args.map s.eval)) callee) :
    SimulationWrites control caller heapLimit code localsTable entries (depth + 1)
      (.call dst fn args)
      ((ABI.callPrefixLocals control f.locals args 0).length + 1 + bodySteps +
        (ABI.returnCodeLocals control f.locals f.result).length + 1)
      s (s.leave callee dst f.result) := by
  refine ⟨simulate_call_exact hcaller hlocals htable hdst hargs hreads hcount
    hresult hresultReads hfunction hcodefit hbody.1, ?_⟩
  intro _ t hm hheap hfit hcode address member
  change CodeAt code t.pc
    (ABI.callCodeLocals control (localsTable fn) (entries fn) dst args t.pc) at hcode
  rw [htable] at hcode
  have hl := callCode_layout hcode
  let returnPC := t.pc + (ABI.callPrefixLocals control f.locals args 0).length + 1
  let prepared := execBlock (ABI.callPrefixLocals control f.locals args returnPC) t
  let entered := prepared.atPC (entries fn)
  have frameMono : ABI.frameSize f.locals ≤ ABI.frameSize control := by
    simp only [ABI.frameSize]
    omega
  have frameEnvelope : (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals ≤
      (t.regs (ABI.sp control)).toNat + (depth + 1) * ABI.frameSize control := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hframeFit : (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals < 2 ^ w :=
    frameEnvelope.trans_lt hfit
  have hp : ABI.CallPreparedLocals control f.locals heapLimit args returnPC s t prepared :=
    ABI.callPrefixLocals_correct hm hcaller hlocals hargs hreads hcount hheap hframeFit
  have hprefix : Exec code (ABI.callPrefixLocals control f.locals args returnPC).length
      t prepared := ABI.callPrefixLocals_exec hl.setup hm.running
  have jumpFetch : code[prepared.pc]? = some (.jump (entries fn)) := by
    rw [hp.pc, ABI.callPrefixLocals_length control f.locals args returnPC 0]
    exact hl.jump
  have hjump : Exec code 1 prepared entered := Exec.jump hp.matched.running jumpFetch
  have henteredSP : (entered.regs (ABI.sp control)).toNat =
      (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals := hp.sp
  have childEnvelope : (entered.regs (ABI.sp control)).toNat +
      depth * ABI.frameSize control ≤
      (t.regs (ABI.sp control)).toNat + (depth + 1) * ABI.frameSize control := by
    rw [henteredSP, Nat.add_mul, Nat.one_mul]
    omega
  have hchildHeap : heapLimit ≤ (entered.regs (ABI.sp control)).toNat := by
    rw [henteredSP]
    omega
  have hchildFit : Compiler.StackFits control depth entered := childEnvelope.trans_lt hfit
  change CodeAt code (entries fn)
    (compileStmt control localsTable entries f.body (entries fn) ++
      ABI.returnCodeLocals control f.locals f.result) at hfunction
  have hbodyAt : CodeAt code entered.pc
      (compileStmt control localsTable entries f.body entered.pc) := hfunction.append_left
  obtain ⟨q, hbodyExec, hcallee, hbodyFrame, _, hbodyPC⟩ :=
    hbody.1 hlocals entered (hp.matched.atPC (entries fn)) hchildHeap hchildFit hbodyAt
  have hqSP : (q.regs (ABI.sp control)).toNat =
      (t.regs (ABI.sp control)).toNat + ABI.frameSize f.locals := by
    rw [hbodyFrame.sp]
    exact henteredSP
  obtain ⟨hheader, hsaved⟩ := hbody.prefix_savedFrame hlocals
    (hp.matched.atPC (entries fn)) hchildHeap hchildFit hbodyAt
    hheap (by rw [henteredSP]) hp.saved hp.returnAddress (Nat.le_refl _) hbodyExec
  have hreturnAt : CodeAt code q.pc (ABI.returnCodeLocals control f.locals f.result) := by
    rw [hbodyPC]
    simpa only [entered, State.atPC_pc, compileStmt_length] using hfunction.append_right
  have hr := ABI.returnPrefixLocals_correct hlocals hcallee hresult hresultReads
    hframeFit hqSP hsaved hheader
  let restored := execBlock (ABI.returnPrefixLocals control f.locals f.result) q
  let back := restored.atPC returnPC
  have hreturnFit : returnPC < 2 ^ w :=
    Nat.lt_trans (List.getElem?_eq_some_iff.mp hl.receive).1 hcodefit
  have hreturnExec : Exec code (ABI.returnCodeLocals control f.locals f.result).length q back :=
    ABI.returnCodeLocals_exec hr hreturnAt hcallee.running (Word.ofNat_toNat_of_lt hreturnFit)
  rw [← ABI.callPrefixLocals_length control f.locals args returnPC 0] at member
  rw [heapWrites_add (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec) 1,
    Finset.mem_union] at member
  rcases member with beforeReceive | receive
  · rw [heapWrites_add ((hprefix.trans hjump).trans hbodyExec) _, Finset.mem_union]
      at beforeReceive
    rcases beforeReceive with beforeReturn | returning
    · rw [heapWrites_add (hprefix.trans hjump) _, Finset.mem_union] at beforeReturn
      rcases beforeReturn with setupJump | body
      · rw [heapWrites_add hprefix 1, Finset.mem_union] at setupJump
        rcases setupJump with setup | jump
        · rw [ABI.callPrefixLocals_heapWrites_eq_frameSlots
            (hcount.trans hlocals) (fun a ha => (hargs a ha).mono hcaller)
            hl.setup hm.running] at setup
          exact Or.inr ((ABI.mem_frameSlots_iff hframeFit.le).mp setup).1
        · rw [heapWrites_one, stepHeapWrites_of_fetch hp.matched.running jumpFetch] at jump
          exact (Finset.notMem_empty address jump).elim
      · rcases hbody.2 hlocals entered (hp.matched.atPC (entries fn)) hchildHeap hchildFit
          hbodyAt address body with inHeap | inChild
        · exact Or.inl inHeap
        · right
          rw [henteredSP] at inChild
          omega
    · rw [ABI.returnCodeLocals_heapWrites_eq_empty hreturnAt hcallee.running] at returning
      exact (Finset.notMem_empty address returning).elim
  · have backRunning : back.status = .running := hr.status.trans hcallee.running
    have receiveFetch : code[back.pc]? = some (.move dst (ABI.rv control)) := hl.receive
    rw [heapWrites_one, stepHeapWrites_of_fetch backRunning receiveFetch] at receive
    exact (Finset.notMem_empty address receive).elim

end Ram.LocalCompiler
