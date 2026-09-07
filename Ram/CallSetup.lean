/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Frame
import Ram.Arguments

/-!
# Correctness of the concrete call prefix

Arguments are buffered while caller locals remain unchanged. The return word
and original caller locals are then saved, callee locals are initialized, and
the stack pointer advances by a non-wrapping frame size. All effects below are
those of `ABI.callPrefix` itself, not an abstract bulk-call operation.
-/

namespace Ram.ABI

@[simp] theorem saveReturn_regs (n returnPC : Nat) (s : State w) (r : Reg)
    (hr : r ≠ tmp n) :
    (execBlock (saveReturn n returnPC) s).regs r = s.regs r := by
  simp [saveReturn, execBlock, execInstr, State.setReg, State.next, hr]

@[simp] theorem saveReturn_sp (n returnPC : Nat) (s : State w) :
    (execBlock (saveReturn n returnPC) s).regs (sp n) = s.regs (sp n) :=
  saveReturn_regs n returnPC s (sp n) (by simp [sp, tmp])

theorem saveReturn_mem (n returnPC : Nat) (s : State w) (a : Word w) :
    (execBlock (saveReturn n returnPC) s).mem a =
      if a = s.regs (sp n) then BitVec.ofNat w returnPC else s.mem a := by
  simp [saveReturn, execBlock, execInstr, State.setReg, State.setMem, State.next, sp, tmp]

@[simp] theorem saveReturn_same (n returnPC : Nat) (s : State w) :
    (execBlock (saveReturn n returnPC) s).mem (s.regs (sp n)) =
      BitVec.ofNat w returnPC := by
  rw [saveReturn_mem]
  simp

theorem saveReturn_mem_ne (n returnPC : Nat) (s : State w) (a : Word w)
    (ha : a ≠ s.regs (sp n)) :
    (execBlock (saveReturn n returnPC) s).mem a = s.mem a := by
  rw [saveReturn_mem, if_neg ha]

@[simp] theorem saveReturn_input (n returnPC : Nat) (s : State w) :
    (execBlock (saveReturn n returnPC) s).input = s.input := rfl

@[simp] theorem saveReturn_output (n returnPC : Nat) (s : State w) :
    (execBlock (saveReturn n returnPC) s).outputRev = s.outputRev := rfl

@[simp] theorem saveReturn_status (n returnPC : Nat) (s : State w) :
    (execBlock (saveReturn n returnPC) s).status = s.status := rfl

theorem saveReturn_linear (n returnPC : Nat) :
    ∀ instr ∈ saveReturn n returnPC, instr.Linear := by
  simp [saveReturn, Instr.Linear]

theorem saveReturn_matches {n H returnPC : Nat} {s : Source.State w} {t : State w}
    (hm : s.Matches H n t) (hheap : H ≤ (t.regs (sp n)).toNat) :
    s.Matches H n (execBlock (saveReturn n returnPC) t) := by
  refine ⟨?_, ?_, hm.input, hm.output, hm.running⟩
  · intro r hr
    exact (hm.regs r hr).trans
      (saveReturn_regs n returnPC t r (Nat.ne_of_lt (by unfold tmp; omega))).symm
  · intro a ha
    rw [saveReturn_mem_ne n returnPC t a (by
      intro he
      have hn := congrArg (fun x : Word w => x.toNat) he
      change a.toNat = (t.regs (sp n)).toNat at hn
      omega)]
    exact hm.heap a ha

@[simp] theorem advance_sp (n : Nat) (s : State w) :
    (execBlock (advance n) s).regs (sp n) = arrayAddr (s.regs (sp n)) (frameSize n) := by
  simp [advance, execBlock, execInstr, State.setReg, State.next, BinOp.eval,
    arrayAddr, sp, tmp]

theorem advance_sp_toNat (n : Nat) (s : State w)
    (hfit : (s.regs (sp n)).toNat + frameSize n < 2 ^ w) :
    ((execBlock (advance n) s).regs (sp n)).toNat =
      (s.regs (sp n)).toNat + frameSize n := by
  rw [advance_sp]
  exact arrayAddr_toNat hfit

theorem advance_regs (n : Nat) (s : State w) (r : Reg)
    (hs : r ≠ sp n) (ht : r ≠ tmp n) :
    (execBlock (advance n) s).regs r = s.regs r := by
  simp [advance, execBlock, execInstr, State.setReg, State.next, hs, ht]

@[simp] theorem advance_mem (n : Nat) (s : State w) :
    (execBlock (advance n) s).mem = s.mem := rfl

@[simp] theorem advance_input (n : Nat) (s : State w) :
    (execBlock (advance n) s).input = s.input := rfl

@[simp] theorem advance_output (n : Nat) (s : State w) :
    (execBlock (advance n) s).outputRev = s.outputRev := rfl

@[simp] theorem advance_status (n : Nat) (s : State w) :
    (execBlock (advance n) s).status = s.status := rfl

theorem advance_linear (n : Nat) : ∀ instr ∈ advance n, instr.Linear := by
  simp [advance, Instr.Linear]

theorem advance_matches {n H : Nat} {s : Source.State w} {t : State w}
    (hm : s.Matches H n t) : s.Matches H n (execBlock (advance n) t) := by
  refine ⟨?_, hm.heap, hm.input, hm.output, hm.running⟩
  intro r hr
  exact (hm.regs r hr).trans
    (advance_regs n t r (Nat.ne_of_lt hr)
      (Nat.ne_of_lt (by unfold tmp; omega))).symm

theorem saveLocals_matches {n H : Nat} {s : Source.State w} {t : State w}
    (hm : s.Matches H n t) (hheap : H ≤ (t.regs (sp n)).toNat)
    (hfit : (t.regs (sp n)).toNat + n < 2 ^ w) :
    s.Matches H n (execBlock (saveLocals n n) t) := by
  refine ⟨?_, saveLocals_heap t (Nat.le_refl n) hfit hheap hm.heap, ?_, ?_, ?_⟩
  · intro r hr
    exact (hm.regs r hr).trans
      (saveLocals_regs n n t r
        (Nat.ne_of_lt (by unfold addr; omega))
        (Nat.ne_of_lt (by unfold tmp; omega))).symm
  · simpa using hm.input
  · simpa using hm.output
  · simpa using hm.running

theorem callPrefix_linear (n : Nat) (args : List Expr) (returnPC : Nat) :
    ∀ instr ∈ callPrefix n args returnPC, instr.Linear := by
  intro instr hi
  simp only [callPrefix, List.mem_append] at hi
  rcases hi with (((he | hr) | hs) | hi) | ha
  · exact evalArgs_linear n 0 args instr he
  · exact saveReturn_linear n returnPC instr hr
  · exact saveLocals_linear n n instr hs
  · exact initLocals_linear n args.length n instr hi
  · exact advance_linear n instr ha

/-- The concrete target state just before the direct jump to a callee. The
saved frame contains initial caller locals, not the newly installed parameters. -/
structure CallPrepared (n H : Nat) (args : List Expr) (returnPC : Nat)
    (s : Source.State w) (t u : State w) : Prop where
  matched : (s.enter (args.map s.eval)).Matches H n u
  sp : (u.regs (ABI.sp n)).toNat = (t.regs (ABI.sp n)).toNat + frameSize n
  saved : FrameSaved n (t.regs (ABI.sp n)) t.regs u.mem
  returnAddress : u.mem (t.regs (ABI.sp n)) = BitVec.ofNat w returnPC
  below : ∀ a, a.toNat < (t.regs (ABI.sp n)).toNat → u.mem a = t.mem a
  pc : u.pc = t.pc + (callPrefix n args returnPC).length

/-- Every phase of the actual call prefix agrees with entering a source frame.
The heap bound separates all argument reads from compiler-owned stack writes;
the frame-size bound makes the resulting stack pointer exact, without wrapping. -/
theorem callPrefix_correct {n H returnPC : Nat} {args : List Expr}
    {s : Source.State w} {t : State w}
    (hm : s.Matches H n t)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow H s.regs s.mem)
    (hcount : args.length ≤ n)
    (hheap : H ≤ (t.regs (sp n)).toNat)
    (hfit : (t.regs (sp n)).toNat + frameSize n < 2 ^ w) :
    CallPrepared n H args returnPC s t (execBlock (callPrefix n args returnPC) t) := by
  let v0 := execBlock (evalArgs n 0 args) t
  let v1 := execBlock (saveReturn n returnPC) v0
  let v2 := execBlock (saveLocals n n) v1
  let v3 := execBlock (initLocals n args.length n) v2
  let u := execBlock (advance n) v3
  have hu : execBlock (callPrefix n args returnPC) t = u := by
    simp only [callPrefix, execBlock_append, u, v3, v2, v1, v0]
  have he : ArgsEvaluated n 0 args t v0 :=
    evalArgs_correct (by simpa using hcount) hargs t
  have hsp0 : v0.regs (sp n) = t.regs (sp n) :=
    he.control (sp n) (show n < n + 5 by omega)
  have hsp1 : v1.regs (sp n) = t.regs (sp n) :=
    (saveReturn_sp n returnPC v0).trans hsp0
  have hsp2 : v2.regs (sp n) = t.regs (sp n) :=
    (saveLocals_sp n n v1).trans hsp1
  have hlocals1 : ∀ i, i < n → v1.regs i = t.regs i := by
    intro i hi
    exact (saveReturn_regs n returnPC v0 i
      (Nat.ne_of_lt (by unfold tmp; omega))).trans
      (he.control i (by change (i : Nat) < n + 5; omega))
  have hfit1 : (v1.regs (sp n)).toNat + n < 2 ^ w := by
    rw [hsp1]
    unfold frameSize at hfit
    omega
  have hm1 : s.Matches H n v1 :=
    saveReturn_matches (he.matches hm) (by rw [hsp0]; exact hheap)
  have hm2 : s.Matches H n v2 :=
    saveLocals_matches hm1 (by rw [hsp1]; exact hheap) hfit1
  have hframe2 : FrameSaved n (t.regs (sp n)) t.regs v2.mem := by
    have hsaved := saveLocals_frame v1 (Nat.le_refl n) hfit1
    intro i hi
    have hh := (hsaved i hi).trans (hlocals1 i hi)
    simpa only [hsp1] using hh
  have hreturn1 : v1.mem (t.regs (sp n)) = BitVec.ofNat w returnPC := by
    rw [← hsp0]
    exact saveReturn_same n returnPC v0
  have hreturn2 : v2.mem (t.regs (sp n)) = BitVec.ofNat w returnPC := by
    exact (saveLocals_mem_outside v1 (Nat.le_refl n) hfit1 (t.regs (sp n))
      (Or.inl (by rw [hsp1]; exact Nat.le_refl _))).trans hreturn1
  have hbelow2 : ∀ a, a.toNat < (t.regs (sp n)).toNat → v2.mem a = t.mem a := by
    intro a ha
    have hlocal := saveLocals_mem_outside v1 (Nat.le_refl n) hfit1 a
      (Or.inl (by rw [hsp1]; exact Nat.le_of_lt ha))
    have hne : a ≠ v0.regs (sp n) := by
      rw [hsp0]
      intro heq
      have hn := congrArg (fun x : Word w => x.toNat) heq
      change a.toNat = (t.regs (sp n)).toNat at hn
      omega
    exact hlocal.trans ((saveReturn_mem_ne n returnPC v0 a hne).trans (congrFun he.memory a))
  have hbuffer : ∀ (i : Nat) (hi : i < (args.map s.eval).length),
      v2.regs (arg n i) = (args.map s.eval)[i] := by
    intro i hi
    have hi' : i < args.length := by simpa using hi
    have harg1 : v1.regs (arg n i) = v0.regs (arg n i) :=
      saveReturn_regs n returnPC v0 (arg n i)
        (Nat.ne_of_gt (by unfold arg tmp; omega))
    have harg2 : v2.regs (arg n i) = v1.regs (arg n i) :=
      saveLocals_arg n n i v1
    have hvalue : v0.regs (arg n i) = s.eval args[i] := by
      simpa only [Nat.zero_add] using he.source_values hm hargs hreads i hi'
    simpa only [List.getElem_map] using harg2.trans (harg1.trans hvalue)
  have hm3 : (s.enter (args.map s.eval)).Matches H n v3 := by
    simpa only [List.length_map] using initLocals_matches hm2 (args.map s.eval) hbuffer
  have hinit := initLocals_correct n args.length n v2
  have hsp3 : v3.regs (sp n) = t.regs (sp n) :=
    (hinit.preserved (sp n) (Nat.le_refl n)).trans hsp2
  have hmem : u.mem = v2.mem := (advance_mem n v3).trans hinit.memory
  have hpc := execBlock_pc (callPrefix n args returnPC) t (callPrefix_linear n args returnPC)
  rw [hu] at hpc ⊢
  refine ⟨advance_matches hm3, ?_, ?_, ?_, ?_, hpc⟩
  · have hfit3 : (v3.regs (sp n)).toNat + frameSize n < 2 ^ w := by
      rw [hsp3]
      exact hfit
    exact (advance_sp_toNat n v3 hfit3).trans (by rw [hsp3])
  · rw [hmem]
    exact hframe2
  · rw [hmem]
    exact hreturn2
  · intro a ha
    rw [hmem]
    exact hbelow2 a ha

/-- The whole setup block executes by the single machine transition rule. -/
theorem callPrefix_exec {code : Code} {n returnPC : Nat} {args : List Expr} {t : State w}
    (hcode : CodeAt code t.pc (callPrefix n args returnPC)) (hrun : t.status = .running) :
    Exec code (callPrefix n args returnPC).length t
      (execBlock (callPrefix n args returnPC) t) :=
  execBlock_exec hcode (callPrefix_linear n args returnPC) hrun

/-- Source-frame refinement paired with execution of the emitted prefix. -/
theorem callPrefix_refines {code : Code} {n H returnPC : Nat} {args : List Expr}
    {s : Source.State w} {t : State w}
    (hm : s.Matches H n t)
    (hargs : ∀ a ∈ args, a.Bounded n)
    (hreads : ∀ a ∈ args, a.ReadsBelow H s.regs s.mem)
    (hcount : args.length ≤ n) (hheap : H ≤ (t.regs (sp n)).toNat)
    (hfit : (t.regs (sp n)).toNat + frameSize n < 2 ^ w)
    (hcode : CodeAt code t.pc (callPrefix n args returnPC)) :
    ∃ u, Exec code (callPrefix n args returnPC).length t u ∧
      CallPrepared n H args returnPC s t u := by
  exact ⟨_, callPrefix_exec hcode hm.running,
    callPrefix_correct hm hargs hreads hcount hheap hfit⟩

end Ram.ABI
