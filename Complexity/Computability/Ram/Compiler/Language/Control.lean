/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Values
import Complexity.Language.Semantics

/-!
# Preserving values around the return flag

The compiler's return flag is a real register outside the source-variable
layout and the function's result fields. These lemmas use existing register
updates to preserve source values while initializing or setting that flag,
and preserve the flag while receiving fresh binding fields.

No source value observes the flag. Unit continues to have no result field;
separation from a Unit result imposes no fictitious register requirement.
Matching concerns only lexical values and control. Applying it to a source
state's locals does not relate that state's heap to RAM memory.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Normal completion retains the lexical environment; return exposes its
actual fields. The private flag distinguishes these outcomes without requiring
returned executions to preserve source bindings that are no longer live. -/
def ControlMatches (layout : RegisterMap Γ) (resultSlot flag : Reg) (finish : Env Γ)
    (control : Control result) (target : Source.State w) : Prop :=
  match control with
  | .normal => layout.Matches finish target.regs ∧ target.regs flag = 0
  | .returned value =>
      (resultExprs result resultSlot).map target.eval = valueWords w value ∧
        target.regs flag = 1
  | .fault _ => False

/-- Finishing a lexical binding drops only its temporary environment entry. -/
theorem ControlMatches.tail {layout : RegisterMap Γ} {finish : Env (τ :: Γ)}
    {target : Source.State w} {control : Control result}
    (matched : ControlMatches (RegisterMap.extend layout τ dst)
      resultSlot flag finish control target) :
    ControlMatches layout resultSlot flag finish.tail control target := by
  cases control with
  | normal => exact ⟨RegisterMap.Matches.tail matched.1, matched.2⟩
  | returned _ => exact matched
  | fault _ => exact matched

namespace RegisterMap

/-- A compiler-private register is not assigned to any field of a source binding. -/
def Avoids (layout : RegisterMap Γ) (r : Reg) : Prop :=
  ∀ {τ} (v : Var Γ τ) (i : Fin (fieldCount τ)), layout v i ≠ r

/-- Allocating every field after the private register preserves separation. -/
theorem Avoids.extend {layout : RegisterMap Γ} (avoids : layout.Avoids flag)
    (fresh : flag < dst) : Avoids (RegisterMap.extend layout τ dst) flag := by
  intro σ v i
  cases v with
  | here =>
      change dst + i.val ≠ flag
      exact Nat.ne_of_gt (Nat.lt_of_lt_of_le fresh (Nat.le_add_right dst i.val))
  | there v => exact avoids v i

/-- Initializing or updating a private register preserves every represented
source value. This applies equally to the initial zero and the returned flag. -/
theorem Matches.setReg_of_ne {layout : RegisterMap Γ} {env : Env Γ}
    {entry : Source.State w} (matched : layout.Matches env entry.regs)
    (avoids : layout.Avoids r) (value : Word w) :
    layout.Matches env (entry.setReg r value).regs := by
  intro τ v i
  rw [Source.State.setReg_ne entry r (layout v i) value (avoids v i)]
  exact matched v i

end RegisterMap

/-- Receiving fresh fields does not overwrite a distinct private register.
The fields are the actual assigned list; no length or default-value assumption
is required for preservation outside the destinations. -/
theorem valueRegs_setRegs_other (entry : Source.State w) (τ : Ty) (dst flag : Reg)
    (values : List (Word w)) (separate : flag ∉ valueRegs τ dst) :
    (entry.setRegs (valueRegs τ dst) values).regs flag = entry.regs flag := by
  exact Source.State.setRegs_ne entry _ _ flag separate

/-- A private flag before a fresh tuple is outside every allocated field. -/
theorem flag_not_mem_valueRegs_of_lt (τ : Ty) (dst flag : Reg)
    (separate : flag < dst) : flag ∉ valueRegs τ dst := by
  intro member
  exact Nat.not_le_of_gt separate (mem_valueRegs.mp member).1

/-- A flag following the result tuple lies outside all actual result fields. -/
theorem flag_not_mem_valueRegs (τ : Ty) (resultSlot flag : Reg)
    (separate : resultSlot + fieldCount τ ≤ flag) :
    flag ∉ valueRegs τ resultSlot := by
  intro member
  exact Nat.not_le_of_gt (mem_valueRegs.mp member).2 separate

/-- Setting the private flag leaves the already-computed return tuple intact. -/
theorem resultExprs_setReg_eval (τ : Ty) (resultSlot flag : Reg) (value : Word w)
    (entry : Source.State w) (separate : flag ∉ valueRegs τ resultSlot) :
    (resultExprs τ resultSlot).map (entry.setReg flag value).eval =
      (resultExprs τ resultSlot).map entry.eval := by
  simp only [resultExprs, List.map_map]
  apply List.map_congr_left
  intro r member
  change (entry.setReg flag value).regs r = entry.regs r
  apply Source.State.setReg_ne
  intro same
  exact separate (same ▸ member)

end Ram.LanguageCompiler
