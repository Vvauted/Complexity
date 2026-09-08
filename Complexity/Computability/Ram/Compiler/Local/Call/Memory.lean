/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.ABI.Memory
import Complexity.Computability.Ram.Compiler.Local.Call.Basic
import Complexity.Computability.Ram.Compiler.Local.Exact.MemoryBasic

/-!
# Actual heap accesses throughout a recursive call

The existing exact call simulation supplies the setup, jump, body, return and
receive transitions. Their actual access sets are joined at those same cuts.
The body's access bound is an induction hypothesis, while both ABI ends use
the concrete callee-sized frame proved in `LocalABI.Memory`.

The envelope uses the entry SP plus the remaining depth times the global frame
size. Actual frames still have the callee's local size; this is a sufficient
address bound, not a changed frame layout or an additional cost model.
-/

namespace Ram.LocalCompiler

/-- Complete call simulation, including all real stack accesses. The body
hypothesis is strengthened only by its actual access bound; exact costs and
the source-state result remain those of `simulate_call_exact`. -/
theorem simulate_call_memory
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
    (hbody : SimulationMemory control f.locals heapLimit code localsTable entries depth
      f.body bodySteps (s.enter (args.map s.eval)) callee) :
    SimulationMemory control caller heapLimit code localsTable entries (depth + 1)
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
  have hheader : q.mem (t.regs (ABI.sp control)) = BitVec.ofNat w returnPC := by
    have below : (t.regs (ABI.sp control)).toNat < (entered.regs (ABI.sp control)).toNat := by
      rw [henteredSP]
      simp [ABI.frameSize]
    rw [hbodyFrame.older (t.regs (ABI.sp control)) hheap below]
    exact hp.returnAddress
  have hsaved : ABI.FrameSaved f.locals (t.regs (ABI.sp control)) t.regs q.mem := by
    intro i hi
    have slotFit : (t.regs (ABI.sp control)).toNat + (i + 1) < 2 ^ w := by
      change (t.regs (ABI.sp control)).toNat + (f.locals + 1) < 2 ^ w at hframeFit
      omega
    have slotAddress := arrayAddr_toNat slotFit
    have lower : heapLimit ≤ (arrayAddr (t.regs (ABI.sp control)) (i + 1)).toNat := by
      rw [slotAddress]
      omega
    have upper : (arrayAddr (t.regs (ABI.sp control)) (i + 1)).toNat <
        (entered.regs (ABI.sp control)).toNat := by
      rw [slotAddress, henteredSP]
      simp only [ABI.frameSize]
      omega
    rw [hbodyFrame.older _ lower upper]
    exact hp.saved i hi
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
  have heapEnvelope : heapLimit ≤
      (t.regs (ABI.sp control)).toNat + (depth + 1) * ABI.frameSize control := by omega
  rw [← ABI.callPrefixLocals_length control f.locals args returnPC 0] at member
  rw [heapAccesses_add (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec) 1,
    Finset.mem_union] at member
  rcases member with beforeReceive | receive
  · rw [heapAccesses_add ((hprefix.trans hjump).trans hbodyExec) _, Finset.mem_union]
      at beforeReceive
    rcases beforeReceive with beforeReturn | returning
    · rw [heapAccesses_add (hprefix.trans hjump) _, Finset.mem_union] at beforeReturn
      rcases beforeReturn with setupJump | body
      · rw [heapAccesses_add hprefix 1, Finset.mem_union] at setupJump
        rcases setupJump with setup | jump
        · have targetReads : ∀ a ∈ args, a.ReadsBelow heapLimit t.regs t.mem :=
            fun a ha => Expr.readsBelow_congr (hargs a ha) (hreads a ha) hm.regs hm.heap
          rcases ABI.callPrefixLocals_heapAccesses_bounded hlocals hcount
            (fun a ha => (hargs a ha).mono hcaller) targetReads hframeFit
            hl.setup hm.running setup with sourceAccess | frameAccess
          · exact sourceAccess.trans_le heapEnvelope
          · exact frameAccess.2.trans_le frameEnvelope
        · rw [heapAccesses_one, stepHeapAccesses_of_fetch hp.matched.running jumpFetch] at jump
          exact (Finset.notMem_empty address jump).elim
      · exact (hbody.2 hlocals entered (hp.matched.atPC (entries fn)) hchildHeap hchildFit
          hbodyAt address body).trans_le childEnvelope
    · have targetReads : f.result.ReadsBelow heapLimit q.regs q.mem :=
        Expr.readsBelow_congr hresult hresultReads hcallee.regs hcallee.heap
      rcases ABI.returnCodeLocals_heapAccesses_bounded hlocals hresult targetReads
        hqSP hframeFit hreturnAt hcallee.running returning with sourceAccess | frameAccess
      · exact sourceAccess.trans_le heapEnvelope
      · exact frameAccess.2.trans_le frameEnvelope
  · have backRunning : back.status = .running := hr.status.trans hcallee.running
    have receiveFetch : code[back.pc]? = some (.move dst (ABI.rv control)) := hl.receive
    rw [heapAccesses_one, stepHeapAccesses_of_fetch backRunning receiveFetch] at receive
    exact (Finset.notMem_empty address receive).elim

end Ram.LocalCompiler
