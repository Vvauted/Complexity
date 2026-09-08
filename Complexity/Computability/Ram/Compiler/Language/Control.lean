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

/-- A compiler-private register is not assigned to any scalar source binding. -/
def Avoids (layout : RegisterMap Γ) (r : Reg) : Prop :=
  ∀ {τ} (scalar : Scalar τ) (v : Var Γ τ), layout scalar v ≠ r

/-- Allocating a binding away from the private register preserves separation. -/
theorem Avoids.extend {layout : RegisterMap Γ} (avoids : layout.Avoids flag)
    (fresh : dst ≠ flag) : Avoids (RegisterMap.extend layout τ dst) flag := by
  intro σ scalar v
  cases v with
  | here => exact fresh
  | there v => exact avoids scalar v

/-- Initializing or updating a private register preserves every represented
source value. This applies equally to the initial zero and the returned flag. -/
theorem Matches.setReg_of_ne {layout : RegisterMap Γ} {env : Env Γ}
    {entry : Source.State w} (matched : layout.Matches env entry.regs)
    (avoids : layout.Avoids r) (value : Word w) :
    layout.Matches env (entry.setReg r value).regs := by
  intro τ scalar v
  rw [Source.State.setReg_ne entry r (layout scalar v) value (avoids scalar v)]
  exact matched scalar v

end RegisterMap

/-- Receiving fresh fields does not overwrite a distinct private register.
The fields are the actual assigned list; no length or default-value assumption
is required for preservation outside the destinations. -/
theorem valueRegs_setRegs_other (entry : Source.State w) (τ : Ty) (dst flag : Reg)
    (values : List (Word w)) (separate : dst ≠ flag) :
    (entry.setRegs (valueRegs τ dst) values).regs flag = entry.regs flag := by
  apply Source.State.setRegs_ne
  cases τ with
  | nat | bool =>
      simpa only [valueRegs, List.mem_singleton] using Ne.symm separate
  | unit => exact List.not_mem_nil

/-- A flag following the result tuple lies outside all actual result fields. -/
theorem flag_not_mem_valueRegs (τ : Ty) (resultSlot flag : Reg)
    (separate : resultSlot + fieldCount τ ≤ flag) :
    flag ∉ valueRegs τ resultSlot := by
  cases τ with
  | nat | bool =>
      have greater : resultSlot < flag :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self resultSlot) separate
      simpa only [valueRegs, List.mem_singleton] using Nat.ne_of_gt greater
  | unit => exact List.not_mem_nil

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
