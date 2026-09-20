/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering

/-!
# Evaluation of lowered value fields

Atomic values, primitives, arguments and results expose their actual represented
fields through ordinary RAM expressions. These expressions perform no heap reads.
Their exact evaluation reuses the scalar compiler correspondence and the source
operands' word ranges; mathematical placement is not an emitted operation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {placement : Nat → Word w}

/-- Materializing a value field only observes a local register or a literal. -/
theorem atomFieldExpr_readsBelow (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (i : Fin (fieldCount τ)) (entry : Source.State w) :
    (atomFieldExpr layout atom i).ReadsBelow heapLimit entry.regs entry.mem := by
  cases atom with
  | var | nat | bool => trivial
  | unit => exact Fin.elim0 i

/-- Scalar atoms perform no memory reads. -/
theorem atomExpr_readsBelow (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (scalar : Scalar τ) (entry : Source.State w) :
    (atomExpr layout atom scalar).ReadsBelow heapLimit entry.regs entry.mem :=
  atomFieldExpr_readsBelow layout atom scalar.index entry

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
  | length buffer => exact atomFieldExpr_readsBelow layout buffer ⟨1, by change 1 < 2; decide⟩ entry
  | fst pair | snd pair => exact atomFieldExpr_readsBelow layout pair _ entry
  | pair | none | some => cases scalar

/-- A primitive's fields contain no implicit heap traversal. -/
theorem primFieldExpr_readsBelow (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (i : Fin (fieldCount τ)) (entry : Source.State w) :
    (primFieldExpr layout prim i).ReadsBelow heapLimit entry.regs entry.mem := by
  cases prim with
  | atom atom => exact atomFieldExpr_readsBelow layout atom i entry
  | add a b => exact primExpr_readsBelow layout (.add a b) .nat entry
  | mul a b => exact primExpr_readsBelow layout (.mul a b) .nat entry
  | sub a b => exact primExpr_readsBelow layout (.sub a b) .nat entry
  | div a b => exact primExpr_readsBelow layout (.div a b) .nat entry
  | mod a b => exact primExpr_readsBelow layout (.mod a b) .nat entry
  | length a => exact primExpr_readsBelow layout (.length a) .nat entry
  | eq a b => exact primExpr_readsBelow layout (.eq a b) .bool entry
  | lt a b => exact primExpr_readsBelow layout (.lt a b) .bool entry
  | le a b => exact primExpr_readsBelow layout (.le a b) .bool entry
  | pair left right =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left] using
          atomFieldExpr_readsBelow layout left j entry
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right] using
          atomFieldExpr_readsBelow layout right j entry
  | fst pair | snd pair => exact atomFieldExpr_readsBelow layout pair _ entry
  | none τ => trivial
  | some value =>
      refine Fin.cases True.intro ?_ i
      intro j
      exact atomFieldExpr_readsBelow layout value j entry

/-- An option tag is an ordinary field observation, not a heap read. -/
theorem optionTagExpr_readsBelow (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (entry : Source.State w) :
    (optionTagExpr layout value).ReadsBelow heapLimit entry.regs entry.mem :=
  atomFieldExpr_readsBelow layout value ⟨0, Nat.zero_lt_succ _⟩ entry

/-- All fields selected for a primitive result are free of memory reads. -/
theorem primExprs_readsBelow (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (entry : Source.State w) :
    ∀ expr ∈ primExprs layout prim, expr.ReadsBelow heapLimit entry.regs entry.mem := by
  intro expr member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact primFieldExpr_readsBelow layout prim i entry

/-- Materializing an optional payload does not read the heap. -/
theorem optionPayloadExprs_readsBelow (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (entry : Source.State w) :
    ∀ expr ∈ optionPayloadExprs layout value,
      expr.ReadsBelow heapLimit entry.regs entry.mem := by
  intro expr member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact atomFieldExpr_readsBelow layout value i.succ entry

/-- Every actual field of an atomic argument is free of memory reads. -/
theorem atomExprs_readsBelow (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (entry : Source.State w) :
    ∀ expr ∈ atomExprs layout atom, expr.ReadsBelow heapLimit entry.regs entry.mem := by
  intro expr member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact atomFieldExpr_readsBelow layout atom i entry

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

/-- Each represented field evaluates to its exact word encoding. The placement
is only part of the relation, never an operand of the emitted expression. -/
theorem atomFieldExpr_eval (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env)) (i : Fin (fieldCount τ)) :
    entry.eval (atomFieldExpr layout atom i) =
      BitVec.ofNat w (valueField placement (atom.eval env) i) := by
  apply BitVec.eq_of_toNat_eq
  exact (atomFieldExpr_toNat layout atom env entry.regs entry.mem matched fits i).trans
    (Word.ofNat_toNat_of_lt (fits.fields placement i)).symm

/-- An in-range scalar atom evaluates to its exact mathematical encoding. -/
theorem atomExpr_eval (layout : RegisterMap Γ) (atom : Atom Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env)) :
    entry.eval (atomExpr layout atom scalar) =
      BitVec.ofNat w (scalar.toNat (atom.eval env)) := by
  apply BitVec.eq_of_toNat_eq
  exact (atomExpr_toNat layout atom scalar env entry.regs entry.mem hw matched fits).trans
    (Word.ofNat_toNat_of_lt ((Scalar.fits_iff scalar (atom.eval env)).mp fits)).symm

/-- Recover the actual encoded primitive result from the proved scalar
correspondence, without reproving any operation's arithmetic. -/
theorem primExpr_eval (layout : RegisterMap Γ) (prim : Prim Γ τ) (scalar : Scalar τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim) :
    entry.eval (primExpr layout prim scalar) =
      BitVec.ofNat w (scalar.toNat (prim.eval env)) := by
  have observed := primExpr_toNat layout prim scalar env entry.regs entry.mem hw matched fits
  have resultFits : scalar.toNat (prim.eval env) < 2 ^ w :=
    observed ▸ (entry.eval (primExpr layout prim scalar)).isLt
  exact BitVec.eq_of_toNat_eq (observed.trans (Word.ofNat_toNat_of_lt resultFits).symm)

/-- Every materialized primitive field has the exact represented word. -/
theorem primFieldExpr_eval (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (i : Fin (fieldCount τ)) :
    entry.eval (primFieldExpr layout prim i) =
      BitVec.ofNat w (valueField placement (prim.eval env) i) := by
  have observed := primFieldExpr_toNat layout prim env entry.regs entry.mem hw matched fits i
  have resultFits : valueField placement (prim.eval env) i < 2 ^ w :=
    observed ▸ (entry.eval (primFieldExpr layout prim i)).isLt
  exact BitVec.eq_of_toNat_eq (observed.trans (Word.ofNat_toNat_of_lt resultFits).symm)

/-- Flattening a primitive gives exactly its mathematical result's actual fields. -/
theorem primExprs_eval (layout : RegisterMap Γ) (prim : Prim Γ τ) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w) (matched : layout.Matches placement env entry.regs)
    (fits : PrimFits w env prim) :
    (primExprs layout prim).map entry.eval = valueWords placement (prim.eval env) := by
  simp only [primExprs, valueWords, List.map_ofFn]
  congr 1
  funext i
  exact primFieldExpr_eval layout prim env entry hw matched fits i

/-- The represented absent constructor has exactly the zero tag. -/
theorem optionTagExpr_eval_none (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (env : Env Γ) (entry : Source.State w)
    (matched : layout.Matches placement env entry.regs) (selected : value.eval env = none) :
    entry.eval (optionTagExpr layout value) = 0 := by
  cases value with
  | var v =>
      change env.get v = none at selected
      apply BitVec.eq_of_toNat_eq
      simpa only [optionTagExpr, atomFieldExpr, Source.State.eval, Expr.eval,
        selected, valueField_none, BitVec.toNat_zero] using
          matched v ⟨0, Nat.zero_lt_succ _⟩

/-- The represented present constructor has exactly the one tag. -/
theorem optionTagExpr_eval_some (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (env : Env Γ) (entry : Source.State w)
    (matched : layout.Matches placement env entry.regs)
    (selected : value.eval env = some payload) :
    entry.eval (optionTagExpr layout value) = 1 := by
  cases value with
  | var v =>
      change env.get v = some payload at selected
      have tag : (entry.regs (layout v ⟨0, Nat.zero_lt_succ _⟩)).toNat = 1 := by
        simpa only [selected, valueField_some_zero] using
          matched v ⟨0, Nat.zero_lt_succ _⟩
      apply BitVec.eq_of_toNat_eq
      exact tag.trans (Word.ofNat_toNat_of_lt
        (tag ▸ (entry.regs (layout v ⟨0, Nat.zero_lt_succ _⟩)).isLt)).symm

/-- Selected payload fields retain the actual source payload, including borrowed views. -/
theorem optionPayloadExprs_eval (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (env : Env Γ) (entry : Source.State w)
    (matched : layout.Matches placement env entry.regs)
    (selected : value.eval env = some payload) (payloadFits : ValueFits w payload) :
    (optionPayloadExprs layout value).map entry.eval = valueWords placement payload := by
  cases value with
  | var v =>
      change env.get v = some payload at selected
      simp only [optionPayloadExprs, valueWords, List.map_ofFn]
      congr 1
      funext i
      apply BitVec.eq_of_toNat_eq
      have field := matched v i.succ
      simp only [selected, valueField_some_succ] at field
      exact field.trans (Word.ofNat_toNat_of_lt (payloadFits.fields placement i)).symm

/-- The emitted atomic fields encode precisely the source atom, including the
empty Unit tuple. -/
theorem atomExprs_eval (layout : RegisterMap Γ) (atom : Atom Γ τ) (env : Env Γ)
    (entry : Source.State w) (_hw : 0 < w) (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env)) :
    (atomExprs layout atom).map entry.eval = valueWords placement (atom.eval env) := by
  apply List.ext_getElem
  · simp only [List.length_map, atomExprs_length, valueWords_length]
  · intro i _ bound
    simpa only [atomExprs, valueWords, List.getElem_map, List.getElem_ofFn] using
      atomFieldExpr_eval layout atom env entry matched fits
        ⟨i, by simpa only [valueWords_length] using bound⟩

/-- Actual call operands initialize exactly the independent callee environment. -/
theorem argsExprs_eval (layout : RegisterMap Γ) (args : Args Γ params) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w) (matched : layout.Matches placement env entry.regs)
    (fits : EnvFits w (args.eval env)) :
    (argsExprs layout args).map entry.eval = envWords placement (args.eval env) := by
  induction args with
  | nil => rfl
  | cons atom rest ih =>
      simp only [argsExprs, List.map_append, Args.eval, envWords_cons]
      rw [atomExprs_eval layout atom env entry hw matched (fits .here),
        ih (fun v => fits (.there v))]

end Ram.LanguageCompiler
