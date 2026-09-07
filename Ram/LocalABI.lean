/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.CodeLength
import Ram.CallSetup

/-!
# Callee-sized concrete calling-convention code

`control` determines reserved register names; `locals` is the current callee's
local-register bound. Only the latter determines save, initialization, restore,
and stack-frame sizes. The instruction vocabulary and per-transition counting
are unchanged. Existing global-frame entry points are intentionally untouched.
-/

namespace Ram.Expr

/-- Relocating an expression's scratch registers changes no instruction count. -/
theorem compile_length_eq (e : Expr) (a b : Reg) :
    (e.compile a).length = (e.compile b).length := by
  induction e generalizing a b with
  | const => rfl
  | var => rfl
  | bin op lhs rhs ihl ihr =>
      simp only [compile, List.length_append, List.length_singleton]
      rw [ihl a b, ihr (a + 1) (b + 1)]
  | load e ih =>
      simp only [compile, List.length_append, List.length_singleton]
      rw [ih a b]

end Ram.Expr

namespace Ram.ABI

def advanceLocals (control locals : Nat) : Code :=
  [.const (tmp control) (frameSize locals),
    .binop .add (sp control) (sp control) (tmp control)]

def retreatLocals (control locals : Nat) : Code :=
  [.const (tmp control) (frameSize locals),
    .binop .sub (sp control) (sp control) (tmp control)]

def callPrefixLocals (control locals : Nat) (args : List Expr) (returnPC : Nat) : Code :=
  evalArgs control 0 args ++ saveReturn control returnPC ++ saveLocals control locals ++
    initLocals control args.length locals ++ advanceLocals control locals

def callCodeLocals (control locals entry dst : Nat) (args : List Expr) (base : Nat) : Code :=
  let returnPC := base + (callPrefixLocals control locals args 0).length + 1
  callPrefixLocals control locals args returnPC ++ [.jump entry, .move dst (rv control)]

def returnPrefixLocals (control locals : Nat) (result : Expr) : Code :=
  result.compile (scratch control) ++ [.move (rv control) (scratch control)] ++
    retreatLocals control locals ++ [.load (ra control) (sp control)] ++
    restoreLocals control locals

def returnCodeLocals (control locals : Nat) (result : Expr) : Code :=
  returnPrefixLocals control locals result ++ [.jumpReg (ra control)]

theorem advanceLocals_linear (control locals : Nat) :
    ∀ i ∈ advanceLocals control locals, i.Linear := by
  simp [advanceLocals, Instr.Linear]

theorem retreatLocals_linear (control locals : Nat) :
    ∀ i ∈ retreatLocals control locals, i.Linear := by
  simp [retreatLocals, Instr.Linear]

theorem callPrefixLocals_linear (control locals : Nat) (args : List Expr) (returnPC : Nat) :
    ∀ i ∈ callPrefixLocals control locals args returnPC, i.Linear := by
  intro i hi
  simp only [callPrefixLocals, List.mem_append] at hi
  rcases hi with (((he | hr) | hs) | hi) | ha
  · exact evalArgs_linear control 0 args i he
  · exact saveReturn_linear control returnPC i hr
  · exact saveLocals_linear control locals i hs
  · exact initLocals_linear control args.length locals i hi
  · exact advanceLocals_linear control locals i ha

theorem returnPrefixLocals_linear (control locals : Nat) (result : Expr) :
    ∀ i ∈ returnPrefixLocals control locals result, i.Linear := by
  intro i hi
  simp only [returnPrefixLocals, List.mem_append, List.mem_singleton] at hi
  rcases hi with (((he | rfl) | ht) | rfl) | hl
  · exact result.compile_linear (scratch control) i he
  · trivial
  · exact retreatLocals_linear control locals i ht
  · trivial
  · exact restoreLocals_linear control locals i hl

@[simp] theorem advanceLocals_sp (control locals : Nat) (s : State w) :
    (execBlock (advanceLocals control locals) s).regs (sp control) =
      arrayAddr (s.regs (sp control)) (frameSize locals) := by
  simp [advanceLocals, execBlock, execInstr, State.setReg, State.next, BinOp.eval,
    arrayAddr, sp, tmp]

theorem advanceLocals_sp_toNat (control locals : Nat) (s : State w)
    (hfit : (s.regs (sp control)).toNat + frameSize locals < 2 ^ w) :
    ((execBlock (advanceLocals control locals) s).regs (sp control)).toNat =
      (s.regs (sp control)).toNat + frameSize locals := by
  rw [advanceLocals_sp]
  exact arrayAddr_toNat hfit

theorem advanceLocals_regs (control locals : Nat) (s : State w) (r : Reg)
    (hs : r ≠ sp control) (ht : r ≠ tmp control) :
    (execBlock (advanceLocals control locals) s).regs r = s.regs r := by
  simp [advanceLocals, execBlock, execInstr, State.setReg, State.next, hs, ht]

theorem retreatLocals_regs (control locals : Nat) (s : State w) (r : Reg)
    (hs : r ≠ sp control) (ht : r ≠ tmp control) :
    (execBlock (retreatLocals control locals) s).regs r = s.regs r := by
  simp [retreatLocals, execBlock, execInstr, State.setReg, State.next, hs, ht]

/-- A variable-size frame is undone by the actual unsigned subtraction code. -/
theorem retreatLocals_sp (control locals : Nat) (s : State w) (base : Word w)
    (hsp : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (hfit : base.toNat + frameSize locals < 2 ^ w) :
    (execBlock (retreatLocals control locals) s).regs (sp control) = base := by
  have hc : (BitVec.ofNat w (frameSize locals)).toNat = frameSize locals :=
    Word.ofNat_toNat_of_lt
      (Nat.lt_of_le_of_lt (Nat.le_add_left (frameSize locals) base.toNat) hfit)
  have hle : (BitVec.ofNat w (frameSize locals)).toNat ≤ (s.regs (sp control)).toNat := by
    rw [hc, hsp]
    exact Nat.le_add_left _ _
  have hv : BinOp.eval .sub (s.regs (sp control)) (BitVec.ofNat w (frameSize locals)) = base := by
    apply BitVec.eq_of_toNat_eq
    rw [BinOp.eval_sub_toNat_of_le _ _ hle, hc, hsp, Nat.add_sub_cancel]
  have hst : sp control ≠ tmp control := by simp [sp, tmp]
  simpa [retreatLocals, execBlock, execInstr, State.setReg, State.next, hst] using hv

@[simp] theorem advanceLocals_mem (control locals : Nat) (s : State w) :
    (execBlock (advanceLocals control locals) s).mem = s.mem := rfl

@[simp] theorem retreatLocals_mem (control locals : Nat) (s : State w) :
    (execBlock (retreatLocals control locals) s).mem = s.mem := rfl

@[simp] theorem advanceLocals_input (control locals : Nat) (s : State w) :
    (execBlock (advanceLocals control locals) s).input = s.input := rfl

@[simp] theorem advanceLocals_output (control locals : Nat) (s : State w) :
    (execBlock (advanceLocals control locals) s).outputRev = s.outputRev := rfl

@[simp] theorem advanceLocals_status (control locals : Nat) (s : State w) :
    (execBlock (advanceLocals control locals) s).status = s.status := rfl

@[simp] theorem retreatLocals_input (control locals : Nat) (s : State w) :
    (execBlock (retreatLocals control locals) s).input = s.input := rfl

@[simp] theorem retreatLocals_output (control locals : Nat) (s : State w) :
    (execBlock (retreatLocals control locals) s).outputRev = s.outputRev := rfl

@[simp] theorem retreatLocals_status (control locals : Nat) (s : State w) :
    (execBlock (retreatLocals control locals) s).status = s.status := rfl

theorem callPrefixLocals_length (control locals : Nat) (args : List Expr) (a b : Nat) :
    (callPrefixLocals control locals args a).length =
      (callPrefixLocals control locals args b).length := by
  simp [callPrefixLocals, saveReturn]

theorem callCodeLocals_length (control locals entry dst : Nat) (args : List Expr) (base : Nat) :
    (callCodeLocals control locals entry dst args base).length =
      (callPrefixLocals control locals args 0).length + 2 := by
  simp only [callCodeLocals, List.length_append, List.length_cons, List.length_nil]
  rw [callPrefixLocals_length control locals args _ 0]

theorem callPrefixLocals_length_eq (control locals : Nat) (args : List Expr) (returnPC : Nat) :
    (callPrefixLocals control locals args returnPC).length =
      (args.map (fun e => (e.compile (scratch control)).length)).sum +
        args.length + 4 * locals + 4 := by
  simp only [callPrefixLocals, List.length_append, evalArgs_length, saveReturn,
    List.length_cons, List.length_nil, saveLocals_length, initLocals_length, advanceLocals]
  omega

theorem returnPrefixLocals_length (control locals : Nat) (result : Expr) :
    (returnPrefixLocals control locals result).length =
      (result.compile (scratch control)).length + 3 * locals + 4 := by
  simp only [returnPrefixLocals, List.length_append, List.length_cons, List.length_nil,
    retreatLocals, restoreLocals_length]
  omega

theorem returnCodeLocals_length (control locals : Nat) (result : Expr) :
    (returnCodeLocals control locals result).length =
      (result.compile (scratch control)).length + 3 * locals + 5 := by
  simp only [returnCodeLocals, List.length_append, List.length_singleton,
    returnPrefixLocals_length]

/-- The complete local-frame call's instruction count depends on the callee's
local bound, not the largest unrelated function. Expression destinations have
the same generated length, as `Expr.compile_length_eq` states. -/
theorem callLocals_steps_eq (control locals : Nat) (args : List Expr) (result : Expr)
    (returnPC bodySteps : Nat) :
    (callPrefixLocals control locals args returnPC).length + 1 + bodySteps +
        (returnCodeLocals control locals result).length + 1 =
      (args.map (fun e => (e.compile (scratch control)).length)).sum + bodySteps +
        (result.compile (scratch control)).length + 7 * locals + args.length + 11 := by
  rw [callPrefixLocals_length_eq, returnCodeLocals_length]
  omega

theorem callPrefixLocals_exec {code : Code} {control locals returnPC : Nat}
    {args : List Expr} {s : State w}
    (hcode : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (hrun : s.status = .running) :
    Exec code (callPrefixLocals control locals args returnPC).length s
      (execBlock (callPrefixLocals control locals args returnPC) s) :=
  execBlock_exec hcode (callPrefixLocals_linear control locals args returnPC) hrun

theorem returnPrefixLocals_exec {code : Code} {control locals : Nat} {result : Expr}
    {s : State w} (hcode : CodeAt code s.pc (returnPrefixLocals control locals result))
    (hrun : s.status = .running) :
    Exec code (returnPrefixLocals control locals result).length s
      (execBlock (returnPrefixLocals control locals result) s) :=
  execBlock_exec hcode (returnPrefixLocals_linear control locals result) hrun

end Ram.ABI
