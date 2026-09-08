/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.ABI.Basic
import Complexity.Computability.Ram.Compiler.Local.Effects

/-!
# Entering a callee-sized local frame

The caller's source-local bound, the callee's local bound, and the reserved
control-register base are distinct. Argument evaluation preserves all user
registers; only the callee's register interval is saved and initialized.
Registers above that interval remain available to older callers, including
through recursive calls to functions with different local-register bounds.
-/

namespace Ram.ABI

private theorem user_lt_controls {control r : Nat} (h : r < control) :
    r < control + 5 := by omega

private theorem user_ne_sp {control r : Nat} (h : r < control) : r ≠ sp control :=
  Nat.ne_of_lt h

private theorem user_ne_tmp {control r : Nat} (h : r < control) : r ≠ tmp control := by
  unfold tmp
  omega

private theorem user_ne_addr {control r : Nat} (h : r < control) : r ≠ addr control := by
  unfold addr
  omega

private theorem arg_ne_tmp (control i : Nat) : arg control i ≠ tmp control := by
  apply Nat.ne_of_gt
  unfold arg tmp
  omega

theorem ArgsEvaluated.matches_locals {control caller start heapLimit : Nat}
    {args : List Expr} {source : Source.State w} {s t : State w}
    (h : ArgsEvaluated control start args s t)
    (hs : source.Matches heapLimit caller s) (hcaller : caller ≤ control) :
    source.Matches heapLimit caller t := by
  refine ⟨?_, ?_, hs.input.trans h.input.symm, hs.output.trans h.output.symm,
    h.status.trans hs.running⟩
  · intro r hr
    exact (hs.regs r hr).trans
      (h.control r (user_lt_controls (Nat.lt_of_lt_of_le hr hcaller))).symm
  · rw [h.memory]
    exact hs.heap

theorem ArgsEvaluated.source_values_locals {control caller start heapLimit : Nat}
    {args : List Expr} {source : Source.State w} {s t : State w}
    (h : ArgsEvaluated control start args s t)
    (hs : source.Matches heapLimit caller s)
    (hb : ∀ e ∈ args, e.Bounded caller)
    (hr : ∀ e ∈ args, e.ReadsBelow heapLimit source.regs source.mem)
    (i : Nat) (hi : i < args.length) :
    t.regs (arg control (start + i)) = source.eval args[i] := by
  exact (h.values i hi).trans
    (hs.eval_eq (hb _ (List.getElem_mem hi)) (hr _ (List.getElem_mem hi))).symm

theorem saveReturn_matches_locals {control caller heapLimit returnPC : Nat}
    {s : Source.State w} {t : State w} (hm : s.Matches heapLimit caller t)
    (hcaller : caller ≤ control) (hheap : heapLimit ≤ (t.regs (sp control)).toNat) :
    s.Matches heapLimit caller (execBlock (saveReturn control returnPC) t) := by
  refine ⟨?_, ?_, hm.input, hm.output, hm.running⟩
  · intro r hr
    exact (hm.regs r hr).trans
      (saveReturn_regs control returnPC t r
        (user_ne_tmp (Nat.lt_of_lt_of_le hr hcaller))).symm
  · intro a ha
    rw [saveReturn_mem_ne control returnPC t a (by
      intro he
      have hn := congrArg (fun x : Word w => x.toNat) he
      change a.toNat = (t.regs (sp control)).toNat at hn
      omega)]
    exact hm.heap a ha

theorem saveLocals_matches_locals {control caller locals heapLimit : Nat}
    {s : Source.State w} {t : State w} (hm : s.Matches heapLimit caller t)
    (hcaller : caller ≤ control) (hlocals : locals ≤ control)
    (hheap : heapLimit ≤ (t.regs (sp control)).toNat)
    (hfit : (t.regs (sp control)).toNat + locals < 2 ^ w) :
    s.Matches heapLimit caller (execBlock (saveLocals control locals) t) := by
  refine ⟨?_, saveLocals_heap t hlocals hfit hheap hm.heap, ?_, ?_, ?_⟩
  · intro r hr
    have hrN := Nat.lt_of_lt_of_le hr hcaller
    exact (hm.regs r hr).trans
      (saveLocals_regs control locals t r (user_ne_addr hrN) (user_ne_tmp hrN)).symm
  · simpa using hm.input
  · simpa using hm.output
  · simpa using hm.running

theorem initLocals_enter_locals (control locals : Nat) (source : Source.State w)
    (s : State w) (values : List (Word w))
    (hbuffer : ∀ (i : Nat) (hi : i < values.length), s.regs (arg control i) = values[i])
    (r : Reg) (hr : r < locals) :
    (execBlock (initLocals control values.length locals) s).regs r =
      (source.enter values).regs r := by
  rw [(initLocals_correct control values.length locals s).values r hr]
  by_cases hi : r < values.length
  · rw [if_pos hi, hbuffer r hi]
    simp [Source.State.enter, List.getElem?_eq_getElem hi]
  · rw [if_neg hi]
    simp [Source.State.enter, List.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem initLocals_matches_locals {control caller locals heapLimit : Nat}
    {source : Source.State w} {s : State w} (hs : source.Matches heapLimit caller s)
    (values : List (Word w))
    (hbuffer : ∀ (i : Nat) (hi : i < values.length), s.regs (arg control i) = values[i]) :
    (source.enter values).Matches heapLimit locals
      (execBlock (initLocals control values.length locals) s) := by
  have hc := initLocals_correct control values.length locals s
  refine ⟨?_, ?_, hs.input.trans hc.input.symm, hs.output.trans hc.output.symm,
    hc.status.trans hs.running⟩
  · intro r hr
    exact (initLocals_enter_locals control locals source s values hbuffer r hr).symm
  · rw [Source.State.enter_mem, hc.memory]
    exact hs.heap

theorem advanceLocals_matches {control locals observed heapLimit : Nat}
    {s : Source.State w} {t : State w} (hm : s.Matches heapLimit observed t)
    (hob : observed ≤ control) :
    s.Matches heapLimit observed (execBlock (advanceLocals control locals) t) := by
  refine ⟨?_, hm.heap, hm.input, hm.output, hm.running⟩
  intro r hr
  have hrN := Nat.lt_of_lt_of_le hr hob
  exact (hm.regs r hr).trans (advanceLocals_regs control locals t r
    (user_ne_sp hrN) (user_ne_tmp hrN)).symm

/-- The prepared callee has a matching local frame and a saved copy of every
register it can overwrite. Higher user registers are physically unchanged. -/
structure CallPreparedLocals (control locals heapLimit : Nat) (args : List Expr)
    (returnPC : Nat) (s : Source.State w) (t u : State w) : Prop where
  matched : (s.enter (args.map s.eval)).Matches heapLimit locals u
  sp : (u.regs (ABI.sp control)).toNat =
    (t.regs (ABI.sp control)).toNat + frameSize locals
  saved : FrameSaved locals (t.regs (ABI.sp control)) t.regs u.mem
  returnAddress : u.mem (t.regs (ABI.sp control)) = BitVec.ofNat w returnPC
  below : ∀ a, a.toNat < (t.regs (ABI.sp control)).toNat → u.mem a = t.mem a
  above : RegsPreservedAbove control locals t u
  pc : u.pc = t.pc + (callPrefixLocals control locals args returnPC).length

/-- Correctness of the actual callee-sized setup instruction block. Both local
bounds may be smaller than the global register reservation and may differ. -/
theorem callPrefixLocals_correct {control caller locals heapLimit returnPC : Nat}
    {args : List Expr} {s : Source.State w} {t : State w}
    (hm : s.Matches heapLimit caller t)
    (hcaller : caller ≤ control) (hlocals : locals ≤ control)
    (hargs : ∀ a ∈ args, a.Bounded caller)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ locals)
    (hheap : heapLimit ≤ (t.regs (sp control)).toNat)
    (hfit : (t.regs (sp control)).toNat + frameSize locals < 2 ^ w) :
    CallPreparedLocals control locals heapLimit args returnPC s t
      (execBlock (callPrefixLocals control locals args returnPC) t) := by
  let v0 := execBlock (evalArgs control 0 args) t
  let v1 := execBlock (saveReturn control returnPC) v0
  let v2 := execBlock (saveLocals control locals) v1
  let v3 := execBlock (initLocals control args.length locals) v2
  let u := execBlock (advanceLocals control locals) v3
  have hu : execBlock (callPrefixLocals control locals args returnPC) t = u := by
    simp only [callPrefixLocals, execBlock_append, u, v3, v2, v1, v0]
  have he : ArgsEvaluated control 0 args t v0 :=
    evalArgs_correct (by simpa using Nat.le_trans hcount hlocals)
      (fun e hi => (hargs e hi).mono hcaller) t
  have hsp0 : v0.regs (sp control) = t.regs (sp control) :=
    he.control (sp control) (show control < control + 5 by omega)
  have hsp1 : v1.regs (sp control) = t.regs (sp control) :=
    (saveReturn_sp control returnPC v0).trans hsp0
  have hsp2 : v2.regs (sp control) = t.regs (sp control) :=
    (saveLocals_sp control locals v1).trans hsp1
  have hlocals1 : ∀ i, i < locals → v1.regs i = t.regs i := by
    intro i hi
    have hiN := Nat.lt_of_lt_of_le hi hlocals
    exact (saveReturn_regs control returnPC v0 i (user_ne_tmp hiN)).trans
      (he.control i (user_lt_controls hiN))
  have hfit1 : (v1.regs (sp control)).toNat + locals < 2 ^ w := by
    rw [hsp1]
    unfold frameSize at hfit
    omega
  have hm1 : s.Matches heapLimit caller v1 :=
    saveReturn_matches_locals (he.matches_locals hm hcaller) hcaller
      (by rw [hsp0]; exact hheap)
  have hm2 : s.Matches heapLimit caller v2 :=
    saveLocals_matches_locals hm1 hcaller hlocals (by rw [hsp1]; exact hheap) hfit1
  have hframe2 : FrameSaved locals (t.regs (sp control)) t.regs v2.mem := by
    have hsaved := saveLocals_frame v1 hlocals hfit1
    intro i hi
    have hh := (hsaved i hi).trans (hlocals1 i hi)
    simpa only [hsp1] using hh
  have hreturn1 : v1.mem (t.regs (sp control)) = BitVec.ofNat w returnPC := by
    rw [← hsp0]
    exact saveReturn_same control returnPC v0
  have hreturn2 : v2.mem (t.regs (sp control)) = BitVec.ofNat w returnPC := by
    exact (saveLocals_mem_outside v1 hlocals hfit1 (t.regs (sp control))
      (Or.inl (by rw [hsp1]; exact Nat.le_refl _))).trans hreturn1
  have hbelow2 : ∀ a, a.toNat < (t.regs (sp control)).toNat → v2.mem a = t.mem a := by
    intro a ha
    have hlocal := saveLocals_mem_outside v1 hlocals hfit1 a
      (Or.inl (by rw [hsp1]; exact Nat.le_of_lt ha))
    have hne : a ≠ v0.regs (sp control) := by
      rw [hsp0]
      intro heq
      have hn := congrArg (fun x : Word w => x.toNat) heq
      change a.toNat = (t.regs (sp control)).toNat at hn
      omega
    exact hlocal.trans ((saveReturn_mem_ne control returnPC v0 a hne).trans
      (congrFun he.memory a))
  have hbuffer : ∀ (i : Nat) (hi : i < (args.map s.eval).length),
      v2.regs (arg control i) = (args.map s.eval)[i] := by
    intro i hi
    have hi' : i < args.length := by simpa using hi
    have harg1 : v1.regs (arg control i) = v0.regs (arg control i) :=
      saveReturn_regs control returnPC v0 (arg control i) (arg_ne_tmp control i)
    have harg2 : v2.regs (arg control i) = v1.regs (arg control i) :=
      saveLocals_arg control locals i v1
    have hvalue : v0.regs (arg control i) = s.eval args[i] := by
      simpa only [Nat.zero_add] using he.source_values_locals hm hargs hreads i hi'
    simpa only [List.getElem_map] using harg2.trans (harg1.trans hvalue)
  have hm3 : (s.enter (args.map s.eval)).Matches heapLimit locals v3 := by
    simpa only [List.length_map] using initLocals_matches_locals hm2 (args.map s.eval) hbuffer
  have hinit := initLocals_correct control args.length locals v2
  have hsp3 : v3.regs (sp control) = t.regs (sp control) :=
    (hinit.preserved (sp control) hlocals).trans hsp2
  have hmem : u.mem = v2.mem := (advanceLocals_mem control locals v3).trans hinit.memory
  have habove : RegsPreservedAbove control locals t u := by
    intro r hr hrN
    have h0 : v0.regs r = t.regs r := he.control r (user_lt_controls hrN)
    have h1 : v1.regs r = v0.regs r :=
      saveReturn_regs control returnPC v0 r (user_ne_tmp hrN)
    have h2 : v2.regs r = v1.regs r := saveLocals_regs control locals v1 r
      (user_ne_addr hrN) (user_ne_tmp hrN)
    have h3 : v3.regs r = v2.regs r := hinit.preserved r hr
    have h4 : u.regs r = v3.regs r := advanceLocals_regs control locals v3 r
      (user_ne_sp hrN) (user_ne_tmp hrN)
    exact h4.trans (h3.trans (h2.trans (h1.trans h0)))
  have hpc := execBlock_pc (callPrefixLocals control locals args returnPC) t
    (callPrefixLocals_linear control locals args returnPC)
  rw [hu] at hpc ⊢
  refine ⟨advanceLocals_matches hm3 hlocals, ?_, ?_, ?_, ?_, habove, hpc⟩
  · have hfit3 : (v3.regs (sp control)).toNat + frameSize locals < 2 ^ w := by
      rw [hsp3]
      exact hfit
    exact (advanceLocals_sp_toNat control locals v3 hfit3).trans (by rw [hsp3])
  · rw [hmem]
    exact hframe2
  · rw [hmem]
    exact hreturn2
  · intro a ha
    rw [hmem]
    exact hbelow2 a ha

theorem callPrefixLocals_refines {code : Code} {control caller locals heapLimit returnPC : Nat}
    {args : List Expr} {s : Source.State w} {t : State w}
    (hm : s.Matches heapLimit caller t)
    (hcaller : caller ≤ control) (hlocals : locals ≤ control)
    (hargs : ∀ a ∈ args, a.Bounded caller)
    (hreads : ∀ a ∈ args, a.ReadsBelow heapLimit s.regs s.mem)
    (hcount : args.length ≤ locals)
    (hheap : heapLimit ≤ (t.regs (sp control)).toNat)
    (hfit : (t.regs (sp control)).toNat + frameSize locals < 2 ^ w)
    (hcode : CodeAt code t.pc (callPrefixLocals control locals args returnPC)) :
    ∃ u, Exec code (callPrefixLocals control locals args returnPC).length t u ∧
      CallPreparedLocals control locals heapLimit args returnPC s t u :=
  ⟨_, callPrefixLocals_exec hcode hm.running,
    callPrefixLocals_correct hm hcaller hlocals hargs hreads hcount hheap hfit⟩

end Ram.ABI
