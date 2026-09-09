/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering

/-!
# Executing lowered values and bindings

The scalar expression compiler supplies the arithmetic correspondence. This
module transports it to the existing structured RAM semantics: argument lists
contain the actual source fields, primitive bindings execute real assignments,
and returns populate the declared result fields. Unit has neither a dummy
expression nor a dummy assignment.

These scalar fragments do not read memory. Their safety therefore holds for
every heap boundary and call-depth capacity; their mathematical representation
still requires the actual source operands and intermediates to fit.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Scalar atoms perform no memory reads. -/
theorem atomExpr_readsBelow (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (scalar : Scalar τ) (entry : Source.State w) :
    (atomExpr layout atom scalar).ReadsBelow heapLimit entry.regs entry.mem := by
  cases atom with
  | var | nat | bool => trivial
  | unit => cases scalar

/-- The supported primitive operations only evaluate their scalar operands. -/
theorem primExpr_readsBelow (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (scalar : Scalar τ) (entry : Source.State w) :
    (primExpr layout prim scalar).ReadsBelow heapLimit entry.regs entry.mem := by
  cases prim with
  | atom atom => exact atomExpr_readsBelow layout atom scalar entry
  | add left right | mul left right | div left right | mod left right =>
      exact ⟨atomExpr_readsBelow layout left .nat entry,
        atomExpr_readsBelow layout right .nat entry⟩
  | eq left right | lt left right | le left right =>
      exact ⟨atomExpr_readsBelow layout left .nat entry,
        atomExpr_readsBelow layout right .nat entry⟩
  | sub left right =>
      exact ⟨⟨atomExpr_readsBelow layout left .nat entry,
        atomExpr_readsBelow layout right .nat entry⟩,
        ⟨atomExpr_readsBelow layout right .nat entry,
          atomExpr_readsBelow layout left .nat entry⟩⟩

/-- Every actual field of an atomic argument is free of memory reads. -/
theorem atomExprs_readsBelow (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (entry : Source.State w) :
    ∀ expr ∈ atomExprs layout atom, expr.ReadsBelow heapLimit entry.regs entry.mem := by
  cases τ with
  | nat =>
      simpa only [atomExprs, List.mem_singleton, forall_eq] using
        atomExpr_readsBelow layout atom .nat entry (heapLimit := heapLimit)
  | bool =>
      simpa only [atomExprs, List.mem_singleton, forall_eq] using
        atomExpr_readsBelow layout atom .bool entry (heapLimit := heapLimit)
  | unit => simp only [atomExprs, List.not_mem_nil, false_implies, implies_true]

/-- Flattening an argument tuple introduces no loads. -/
theorem argsExprs_readsBelow (layout : RegisterMap Γ) (args : Args Γ params)
    (entry : Source.State w) :
    ∀ expr ∈ argsExprs layout args, expr.ReadsBelow heapLimit entry.regs entry.mem := by
  induction args with
  | nil => simp only [argsExprs, List.not_mem_nil, false_implies, implies_true]
  | cons atom rest ih =>
      intro expr member
      rcases List.mem_append.mp member with member | member
      · exact atomExprs_readsBelow layout atom entry expr member
      · exact ih expr member

/-- The function result tuple only observes its actual result registers. -/
theorem resultExprs_readsBelow (τ : Ty) (resultSlot : Reg) (entry : Source.State w) :
    ∀ expr ∈ resultExprs τ resultSlot, expr.ReadsBelow heapLimit entry.regs entry.mem := by
  intro expr member
  obtain ⟨register, _, rfl⟩ := List.mem_map.mp member
  trivial

/-- An in-range atom evaluates to the exact word encoding of its source value. -/
theorem atomExpr_eval (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs)
    (fits : valueToNat (atom.eval env) < 2 ^ w) :
    entry.eval (atomExpr layout atom scalar) =
      BitVec.ofNat w (valueToNat (atom.eval env)) := by
  apply BitVec.eq_of_toNat_eq
  exact (atomExpr_toNat layout atom scalar env entry.regs entry.mem hw matched fits).trans
    (Word.ofNat_toNat_of_lt fits).symm

/-- Recover the actual encoded primitive result from the proved scalar
correspondence, without reproving any operation's arithmetic. -/
theorem primExpr_eval (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : PrimFits w env prim) :
    entry.eval (primExpr layout prim scalar) =
      BitVec.ofNat w (valueToNat (prim.eval env)) := by
  have observed := primExpr_toNat layout prim scalar env entry.regs entry.mem hw matched fits
  have resultFits : valueToNat (prim.eval env) < 2 ^ w :=
    observed ▸ (entry.eval (primExpr layout prim scalar)).isLt
  exact BitVec.eq_of_toNat_eq (observed.trans (Word.ofNat_toNat_of_lt resultFits).symm)

/-- The emitted atomic fields encode precisely the source atom, including the
empty Unit tuple. -/
theorem atomExprs_eval (layout : RegisterMap Γ) (atom : Atom Γ τ) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w) (matched : layout.Matches env entry.regs)
    (fits : ∀ i : Fin (fieldCount τ), valueField (atom.eval env) i < 2 ^ w) :
    (atomExprs layout atom).map entry.eval = valueWords w (atom.eval env) := by
  cases τ with
  | nat =>
      simpa only [atomExprs, List.map_cons, List.map_nil, valueWords_nat, valueToNat] using
        congrArg (fun value => [value])
          (atomExpr_eval layout atom .nat env entry hw matched
            ((Scalar.fits_iff .nat (atom.eval env)).mp fits))
  | bool =>
      simpa only [atomExprs, List.map_cons, List.map_nil, valueWords_bool, valueToNat] using
        congrArg (fun value => [value])
          (atomExpr_eval layout atom .bool env entry hw matched
            ((Scalar.fits_iff .bool (atom.eval env)).mp fits))
  | unit => simp only [atomExprs, List.map_nil, valueWords_unit]

/-- Actual call operands initialize exactly the independent callee environment. -/
theorem argsExprs_eval (layout : RegisterMap Γ) (args : Args Γ params) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w) (matched : layout.Matches env entry.regs)
    (fits : EnvFits w (args.eval env)) :
    (argsExprs layout args).map entry.eval = envWords w (args.eval env) := by
  induction args with
  | nil => rfl
  | cons atom rest ih =>
      simp only [argsExprs, List.map_append, Args.eval, envWords_cons]
      rw [atomExprs_eval layout atom env entry hw matched (fun i => fits .here i),
        ih (fun v i => fits (.there v) i)]

/-- A primitive executes the existing assignment or skip rule and produces its
actual encoded fields. This theorem does not assume a time budget. -/
theorem lowerPrim_safe (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : PrimFits w env prim) :
    Source.SafeExec program heapLimit depth (lowerPrim layout dst prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords w (prim.eval env))) := by
  cases τ with
  | nat =>
      change Source.SafeExec _ _ _ (.assign dst (primExpr layout prim .nat)) entry
        (entry.setReg dst (BitVec.ofNat w (valueToNat (prim.eval env))))
      rw [← primExpr_eval layout prim .nat env entry hw matched fits]
      exact .assign (primExpr_readsBelow layout prim .nat entry)
  | bool =>
      change Source.SafeExec _ _ _ (.assign dst (primExpr layout prim .bool)) entry
        (entry.setReg dst (BitVec.ofNat w (valueToNat (prim.eval env))))
      rw [← primExpr_eval layout prim .bool env entry hw matched fits]
      exact .assign (primExpr_readsBelow layout prim .bool entry)
  | unit => exact .skip

/-- Fresh primitive binding extends the existing environment correspondence. -/
theorem lowerPrim_matches (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs) (fits : PrimFits w env prim)
    (bounded : layout.Bounded dst) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) (Env.cons (prim.eval env) env)
      (entry.setRegs (valueRegs τ dst) (valueWords w (prim.eval env))).regs := by
  apply matched.setRegs bounded
  have scalarFits (scalar : Scalar τ) : valueToNat (prim.eval env) < 2 ^ w := by
    have observed := primExpr_toNat layout prim scalar env entry.regs entry.mem hw matched fits
    exact observed ▸ (entry.eval (primExpr layout prim scalar)).isLt
  cases τ with
  | nat => exact (Scalar.fits_iff .nat (prim.eval env)).mpr (scalarFits .nat)
  | bool => exact (Scalar.fits_iff .bool (prim.eval env)).mpr (scalarFits .bool)
  | unit => exact fun i => Fin.elim0 i

/-- Return materialization writes only the source result's actual fields. -/
theorem lowerReturn_safe (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches env entry.regs)
    (fits : ∀ i : Fin (fieldCount τ), valueField (atom.eval env) i < 2 ^ w) :
    Source.SafeExec program heapLimit depth (lowerReturn layout resultSlot atom) entry
      (entry.setRegs (valueRegs τ resultSlot) (valueWords w (atom.eval env))) := by
  cases τ with
  | nat =>
      change Source.SafeExec _ _ _ (.assign resultSlot (atomExpr layout atom .nat)) entry
        (entry.setReg resultSlot (BitVec.ofNat w (valueToNat (atom.eval env))))
      rw [← atomExpr_eval layout atom .nat env entry hw matched
        ((Scalar.fits_iff .nat (atom.eval env)).mp fits)]
      exact .assign (atomExpr_readsBelow layout atom .nat entry)
  | bool =>
      change Source.SafeExec _ _ _ (.assign resultSlot (atomExpr layout atom .bool)) entry
        (entry.setReg resultSlot (BitVec.ofNat w (valueToNat (atom.eval env))))
      rw [← atomExpr_eval layout atom .bool env entry hw matched
        ((Scalar.fits_iff .bool (atom.eval env)).mp fits)]
      exact .assign (atomExpr_readsBelow layout atom .bool entry)
  | unit => exact .skip

/-- Reading the result tuple after receiving its fields recovers those actual
fields, not a value selected from a specification. -/
theorem resultExprs_setRegs_eval (τ : Ty) (resultSlot : Reg) (value : Value τ)
    (entry : Source.State w) :
    (resultExprs τ resultSlot).map
        (entry.setRegs (valueRegs τ resultSlot) (valueWords w value)).eval =
      valueWords w value := by
  apply List.ext_getElem
  · simp only [List.length_map, resultExprs_length, valueWords_length]
  · intro i hi _
    have distinct : (valueRegs τ resultSlot).Nodup := by
      simpa only [valueRegs] using
        (List.nodup_range' (s := resultSlot) (n := fieldCount τ))
    have lengths : (valueRegs τ resultSlot).length = (valueWords w value).length := by
      simp only [valueRegs_length, valueWords_length]
    have index : i < (valueRegs τ resultSlot).length := by
      simpa only [resultExprs, List.length_map] using hi
    simpa only [resultExprs, List.getElem_map, Source.State.eval, Expr.eval] using
      Source.State.setRegs_getElem entry (valueRegs τ resultSlot) (valueWords w value)
        distinct lengths i index

end Ram.LanguageCompiler
