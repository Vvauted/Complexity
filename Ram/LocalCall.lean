import Ram.LocalExact
import Ram.LocalCallSetup
import Ram.LocalCallReturn
import Ram.LocalCompiler

/-!
# Complete calls with callee-sized frames

The concrete setup, body, return, and receive segments compose into one exact
RAM execution. The caller and callee may have different local-register bounds.
Registers above the callee's bound survive its body, while lower registers are
restored from the saved frame. Thus the call restores every caller register
except its explicit result destination, including through nested larger callees.
-/

namespace Ram.LocalCompiler

structure CallLayout (code : Code) (control locals entry dst : Nat)
    (args : List Expr) (base : Nat) : Prop where
  setup : CodeAt code base
    (ABI.callPrefixLocals control locals args
      (base + (ABI.callPrefixLocals control locals args 0).length + 1))
  jump : code[base + (ABI.callPrefixLocals control locals args 0).length]? =
    some (.jump entry)
  receive : code[base + (ABI.callPrefixLocals control locals args 0).length + 1]? =
    some (.move dst (ABI.rv control))

theorem callCode_layout {code : Code} {control locals entry dst base : Nat}
    {args : List Expr}
    (h : CodeAt code base (ABI.callCodeLocals control locals entry dst args base)) :
    CallLayout code control locals entry dst args base := by
  change CodeAt code base
    (ABI.callPrefixLocals control locals args _ ++ [.jump entry, .move dst (ABI.rv control)]) at h
  have ht := h.append_right
  refine ⟨h.append_left, ?_, ?_⟩
  · simpa only [ABI.callPrefixLocals_length control locals args _ 0] using ht.head
  · simpa only [ABI.callPrefixLocals_length control locals args _ 0] using ht.tail.head

/-- The cost is the sum of actual instruction-segment counts. In particular,
saving and restoring the callee's locals is not a bulk or annotated operation. -/
theorem simulate_call_exact
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
    (hbody : SimulationExact control f.locals heapLimit code localsTable entries depth
      f.body bodySteps (s.enter (args.map s.eval)) callee) :
    SimulationExact control caller heapLimit code localsTable entries (depth + 1)
      (.call dst fn args)
      ((ABI.callPrefixLocals control f.locals args 0).length + 1 + bodySteps +
        (ABI.returnCodeLocals control f.locals f.result).length + 1)
      s (s.leave callee dst f.result) := by
  intro _ t hm hheap hfit hcode
  change CodeAt code t.pc
    (ABI.callCodeLocals control (localsTable fn) (entries fn) dst args t.pc) at hcode
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
      ABI.returnCodeLocals control f.locals f.result) at hfunction
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
  have hsaved : ABI.FrameSaved f.locals (t.regs (ABI.sp control)) t.regs q.mem := by
    intro i hi
    have hslotFit : (t.regs (ABI.sp control)).toNat + (i + 1) < 2 ^ w := by
      change (t.regs (ABI.sp control)).toNat + (f.locals + 1) < 2 ^ w at hframeFit
      omega
    have ha := arrayAddr_toNat hslotFit
    have hlo : heapLimit ≤ (arrayAddr (t.regs (ABI.sp control)) (i + 1)).toNat := by
      rw [ha]
      omega
    have hhi : (arrayAddr (t.regs (ABI.sp control)) (i + 1)).toNat <
        (entered.regs (ABI.sp control)).toNat := by
      rw [ha, henteredSP]
      simp only [ABI.frameSize]
      omega
    rw [hbodyFrame.older _ hlo hhi]
    exact hp.saved i hi
  have hreturnAt : CodeAt code q.pc (ABI.returnCodeLocals control f.locals f.result) := by
    rw [hbodyPC]
    simpa only [entered, State.atPC_pc, compileStmt_length] using hfunction.append_right
  have hr := ABI.returnPrefixLocals_correct hlocals hcallee hresult hresultReads
    hframeFit hqSP hsaved hheader
  let restored := execBlock (ABI.returnPrefixLocals control f.locals f.result) q
  let back := restored.atPC returnPC
  let finish := execInstr (.move dst (ABI.rv control)) back
  have hreturnFit : returnPC < 2 ^ w :=
    Nat.lt_trans (List.getElem?_eq_some_iff.mp hl.receive).1 hcodefit
  have hreturnExec : Exec code (ABI.returnCodeLocals control f.locals f.result).length q back :=
    ABI.returnCodeLocals_exec hr hreturnAt hcallee.running (Word.ofNat_toNat_of_lt hreturnFit)
  have hreceive : Exec code 1 back finish :=
    Exec.single (step_of_fetch (hr.status.trans hcallee.running) hl.receive)
  have hfull := (((hprefix.trans hjump).trans hbodyExec).trans hreturnExec).trans hreceive
  have hrestored : ∀ r, r < control → restored.regs r = t.regs r := by
    intro r hrN
    by_cases hrl : r < f.locals
    · exact hr.locals r hrl
    · have hrl' := Nat.le_of_not_gt hrl
      exact (hr.preservedAbove r hrl' hrN).trans
        ((hbodyRegs r hrl' hrN).trans (hp.above r hrl' hrN))
  refine ⟨finish, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ABI.callPrefixLocals_length control f.locals args returnPC 0] using hfull
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro r hrCaller
      change (if r = dst then callee.eval f.result else s.regs r) =
        (if r = dst then restored.regs (ABI.rv control) else restored.regs r)
      by_cases heq : r = dst
      · simp only [if_pos heq]
        exact hr.value.symm
      · simp only [if_neg heq]
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
  · refine ⟨?_, ?_⟩
    · change (back.setReg dst (back.regs (ABI.rv control))).regs (ABI.sp control) =
        t.regs (ABI.sp control)
      have hdstN := Nat.lt_of_lt_of_le hdst hcaller
      have hne : ABI.sp control ≠ dst := Ne.symm (Nat.ne_of_lt hdstN)
      exact (State.setReg_ne back dst (ABI.sp control) (back.regs (ABI.rv control)) hne).trans hr.sp
    · intro a ha hb
      change restored.mem a = t.mem a
      rw [hr.memory]
      have hb' : a.toNat < (entered.regs (ABI.sp control)).toNat := by
        rw [henteredSP]
        omega
      exact (hbodyFrame.older a ha hb').trans (hp.below a hb)
  · intro r hrCaller hrN
    change (if r = dst then restored.regs (ABI.rv control) else restored.regs r) = t.regs r
    have hne : r ≠ dst := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hdst hrCaller))
    rw [if_neg hne]
    exact hrestored r hrN
  · change returnPC + 1 = t.pc + stmtSize control localsTable (.call dst fn args)
    rw [stmtSize_call, htable]
    simp only [returnPC, Nat.add_assoc]

end Ram.LocalCompiler
