/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Compiler.Language.HeapOperation
import Complexity.Computability.Ram.Compiler.Language.Copy

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

/-- An atom's actual fields inherit the source layout's copy-region separation. -/
theorem atomFieldExpr_avoidsRange (layout : RegisterMap Γ) (atom : Atom Γ τ)
    (i : Fin (fieldCount τ)) (separated : layout.AvoidsRange dst count) :
    (atomFieldExpr layout atom i).AvoidsRange dst count := by
  cases atom with
  | var v => exact separated v i
  | nat | bool => trivial
  | unit => exact Fin.elim0 i

/-- Scalar operations retain separation of every live operand field. -/
theorem primExpr_avoidsRange (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (scalar : Scalar τ) (separated : layout.AvoidsRange dst count) :
    (primExpr layout prim scalar).AvoidsRange dst count := by
  have atom {σ : Ty} (a : Atom Γ σ) (i : Fin (fieldCount σ)) :=
    atomFieldExpr_avoidsRange layout a i separated
  cases prim with
  | atom a => exact atom a scalar.index
  | add a b | mul a b | div a b | mod a b | eq a b | lt a b | le a b =>
      exact ⟨atom a _, atom b _⟩
  | sub a b => exact ⟨⟨atom a _, atom b _⟩, ⟨atom b _, atom a _⟩⟩
  | length a => exact atom a _
  | fst a | snd a => exact atom a _
  | pair | none | some => cases scalar

/-- Primitive field copies preserve operands outside the full receiver region. -/
theorem primFieldExpr_avoidsRange (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (i : Fin (fieldCount τ)) (separated : layout.AvoidsRange dst count) :
    (primFieldExpr layout prim i).AvoidsRange dst count := by
  cases prim with
  | atom atom => exact atomFieldExpr_avoidsRange layout atom i separated
  | add a b => exact primExpr_avoidsRange layout (.add a b) .nat separated
  | mul a b => exact primExpr_avoidsRange layout (.mul a b) .nat separated
  | sub a b => exact primExpr_avoidsRange layout (.sub a b) .nat separated
  | div a b => exact primExpr_avoidsRange layout (.div a b) .nat separated
  | mod a b => exact primExpr_avoidsRange layout (.mod a b) .nat separated
  | length a => exact primExpr_avoidsRange layout (.length a) .nat separated
  | eq a b => exact primExpr_avoidsRange layout (.eq a b) .bool separated
  | lt a b => exact primExpr_avoidsRange layout (.lt a b) .bool separated
  | le a b => exact primExpr_avoidsRange layout (.le a b) .bool separated
  | pair left right =>
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left] using
          atomFieldExpr_avoidsRange layout left j separated
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right] using
          atomFieldExpr_avoidsRange layout right j separated
  | fst pair | snd pair => exact atomFieldExpr_avoidsRange layout pair _ separated
  | none τ => trivial
  | some value =>
      refine Fin.cases True.intro ?_ i
      intro j
      exact atomFieldExpr_avoidsRange layout value j separated

/-- Fresh fields or singleton results admit the actual sequential primitive copy. -/
theorem primExprs_copySafe (layout : RegisterMap Γ) (prim : Prim Γ τ) (dst : Reg)
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    (primExprs layout prim).length ≤ 1 ∨ ∀ expr ∈ primExprs layout prim,
      expr.AvoidsRange dst (primExprs layout prim).length := by
  rcases copySafe with singleton | separated
  · exact Or.inl (by simpa only [primExprs_length] using singleton)
  · right
    intro expr member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    simpa only [primExprs_length] using primFieldExpr_avoidsRange layout prim i separated

/-- Fresh payload receivers preserve the option's still-live source fields. -/
theorem optionPayloadExprs_copySafe (layout : RegisterMap Γ) (value : Atom Γ (.option τ))
    (dst : Reg) (bounded : layout.Bounded dst) :
    (optionPayloadExprs layout value).length ≤ 1 ∨
      ∀ expr ∈ optionPayloadExprs layout value,
        expr.AvoidsRange dst (optionPayloadExprs layout value).length := by
  right
  intro expr member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact atomFieldExpr_avoidsRange layout value i.succ
    (fun v j => Or.inl (bounded v j))

/-- Primitive execution given separation of the expressions actually emitted. -/
theorem copyPrim_safe (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (copySafe : (primExprs layout prim).length ≤ 1 ∨
      ∀ expr ∈ primExprs layout prim,
        expr.AvoidsRange dst (primExprs layout prim).length) :
    Source.SafeExec program heapLimit depth (lowerPrim layout dst prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))) := by
  rw [lowerPrim_eq_copyFields]
  have execution := copyFields_safe entry dst (primExprs layout prim)
    (primExprs_readsBelow layout prim entry) copySafe
    (program := program) (heapLimit := heapLimit) (depth := depth)
  rw [primExprs_eval layout prim env entry hw matched fits] at execution
  simpa only [valueRegs, primExprs_length] using execution

/-- One-field copies may overlap; otherwise every copied atom field avoids
the complete receiver interval used by the sequential code. -/
theorem atomExprs_copySafe (layout : RegisterMap Γ) (atom : Atom Γ τ) (dst : Reg)
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    (atomExprs layout atom).length ≤ 1 ∨
      ∀ expr ∈ atomExprs layout atom,
        expr.AvoidsRange dst (atomExprs layout atom).length := by
  rcases copySafe with singleton | separated
  · exact Or.inl (by simpa only [atomExprs_length] using singleton)
  · right
    intro expr member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    simpa only [atomExprs_length] using atomFieldExpr_avoidsRange layout atom i separated

/-- The actual sequential field copy has the encoded endpoint once its source
fields are preserved. No simultaneous-copy semantics is assumed. -/
theorem copyAtom_safe (layout : RegisterMap Γ) (dst : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : ValueFits w (atom.eval env))
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    Source.SafeExec program heapLimit depth (copyFields dst (atomExprs layout atom)) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (atom.eval env))) := by
  have execution := copyFields_safe entry dst (atomExprs layout atom)
    (atomExprs_readsBelow layout atom entry) (atomExprs_copySafe layout atom dst copySafe)
    (program := program) (heapLimit := heapLimit) (depth := depth)
  rw [atomExprs_eval layout atom env entry hw matched fits] at execution
  simpa only [valueRegs, atomExprs_length] using execution

/-- Copying a variable into its own contiguous fields performs real assignments
but preserves the state. The encoded endpoint follows from the original match. -/
theorem copyVar_self_safe (layout : RegisterMap Γ) (target : Var Γ τ) (dst : Reg)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : ValueFits w (env.get target))
    (contiguous : ∀ i : Fin (fieldCount τ), layout target i = dst + i.val) :
    Source.SafeExec program heapLimit depth (copyFields dst (atomExprs layout (.var target)))
      entry (entry.setRegs (valueRegs τ dst) (valueWords placement (env.get target))) := by
  have expressions : atomExprs layout (.var target) = (valueRegs τ dst).map Expr.var := by
    apply List.ext_getElem
    · simp only [atomExprs_length, List.length_map, valueRegs_length]
    · intro i leftBound _
      have bound : i < fieldCount τ := by simpa only [atomExprs_length] using leftBound
      simpa only [atomExprs, valueRegs, List.getElem_ofFn, List.getElem_map,
        List.getElem_range', Nat.one_mul, atomFieldExpr] using
        congrArg Expr.var (contiguous ⟨i, bound⟩)
  have encoded := atomExprs_eval layout (.var target) env entry hw matched fits
  rw [expressions, List.map_map] at encoded
  simp only [Atom.eval] at encoded
  have received : entry.setRegs (valueRegs τ dst) (valueWords placement (env.get target)) =
      entry := by
    rw [← encoded]
    exact Source.State.setRegs_map_regs entry (valueRegs τ dst)
  rw [received, expressions]
  exact (copyFields_self_localMeasured (control := 0) entry dst (fieldCount τ)).erase

/-- A primitive executes its assignments or actual sequential field copy and
produces its encoded fields. This theorem does not assume a time budget. -/
theorem lowerPrim_safe (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    Source.SafeExec program heapLimit depth (lowerPrim layout dst prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))) :=
  copyPrim_safe layout dst prim env entry hw matched fits
    (primExprs_copySafe layout prim dst copySafe)

/-- Atomic fields of a different source type occupy a different lexical region.
This is register separation, not a restriction on aliased borrowed buffers. -/
theorem atomFieldExpr_avoidsTarget (layout : RegisterMap Γ) (target : Var Γ τ)
    (atom : Atom Γ σ) (i : Fin (fieldCount σ)) (regular : layout.Regular)
    (different : τ ≠ σ) :
    (atomFieldExpr layout atom i).AvoidsRange (layout.base target) (fieldCount τ) := by
  cases atom with
  | var source => exact regular.other_type target source different i
  | nat | bool => trivial
  | unit => exact Fin.elim0 i

/-- Assign an existing source variable through its regular field layout.
Distinct variables have disjoint fields; self-assignment executes each field
copy without changing its value. No global avoidance of the target is required. -/
theorem lowerAssign_safe (layout : RegisterMap Γ) (target : Var Γ τ) (value : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env value)
    (regular : layout.Regular) :
    Source.SafeExec program heapLimit depth (lowerAssign layout target value) entry
      (entry.setRegs (valueRegs τ (layout.base target)) (valueWords placement (value.eval env))) := by
  classical
  cases value with
  | add a b | mul a b | sub a b | div a b | mod a b | eq a b | lt a b | le a b | length a =>
      exact lowerPrim_safe layout (layout.base target) _ env entry hw matched fits
        (Or.inl (by decide))
  | atom atom =>
      dsimp only [lowerAssign]
      rw [lowerPrim_eq_copyFields]
      change Source.SafeExec _ _ _ (copyFields (layout.base target) (atomExprs layout atom)) _ _
      cases atom with
      | var source =>
          by_cases same : source = target
          · subst source
            exact copyVar_self_safe layout target (layout.base target) env entry hw
              matched fits (regular.fields target)
          · have separated : ∀ expr ∈ atomExprs layout (.var source),
                expr.AvoidsRange (layout.base target) (atomExprs layout (.var source)).length := by
              intro expr member
              obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
              change layout source i < layout.base target ∨
                layout.base target + (atomExprs layout (.var source)).length ≤ layout source i
              rw [atomExprs_length]
              exact regular.other target source (fun equal => same (eq_of_heq equal).symm) i
            have execution := copyFields_safe entry (layout.base target)
              (atomExprs layout (.var source)) (atomExprs_readsBelow layout (.var source) entry)
              (Or.inr separated) (program := program) (heapLimit := heapLimit) (depth := depth)
            rw [atomExprs_eval layout (.var source) env entry hw matched fits] at execution
            simpa only [Prim.eval, Atom.eval, valueRegs, atomExprs_length] using execution
      | nat n => exact copyAtom_safe layout _ (.nat n) env entry hw matched fits (Or.inl (by decide))
      | bool b => exact copyAtom_safe layout _ (.bool b) env entry hw matched fits (Or.inl (by decide))
      | unit => exact .skip
  | pair left right =>
      apply copyPrim_safe layout _ _ env entry hw matched fits
      right
      intro expr member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      simp only [primExprs_length]
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [primFieldExpr, Fin.addCases_left] using
          atomFieldExpr_avoidsTarget layout target left j regular (Ty.prod_ne_left _ _)
      · intro j
        simpa only [primFieldExpr, Fin.addCases_right] using
          atomFieldExpr_avoidsTarget layout target right j regular (Ty.prod_ne_right _ _)
  | fst pair =>
      apply copyPrim_safe layout _ _ env entry hw matched fits
      right
      intro expr member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      simpa only [primExprs_length, primFieldExpr] using
        atomFieldExpr_avoidsTarget layout target pair (i.castAdd _) regular
          (Ne.symm (Ty.prod_ne_left _ _))
  | snd pair =>
      apply copyPrim_safe layout _ _ env entry hw matched fits
      right
      intro expr member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      simpa only [primExprs_length, primFieldExpr] using
        atomFieldExpr_avoidsTarget layout target pair (i.natAdd _) regular
          (Ne.symm (Ty.prod_ne_right _ _))
  | none τ =>
      apply copyPrim_safe layout _ _ env entry hw matched fits
      right
      intro expr member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      trivial
  | some value =>
      apply copyPrim_safe layout _ _ env entry hw matched fits
      right
      intro expr member
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      simp only [primExprs_length]
      refine Fin.cases True.intro ?_ i
      intro j
      exact atomFieldExpr_avoidsTarget layout target value j regular (Ty.option_ne_self _)

/-- A realized primitive's actual result satisfies the source value range
condition, including a buffer's length rather than a fictitious scalar handle. -/
theorem primExpr_valueFits (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim) :
    ValueFits w (prim.eval env) := by
  apply (valueFits_iff placement (prim.eval env)).mpr
  intro i
  have observed := primFieldExpr_toNat layout prim env entry.regs entry.mem hw matched fits i
  exact observed ▸ (entry.eval (primFieldExpr layout prim i)).isLt

/-- Fresh primitive binding extends the existing environment correspondence. -/
theorem lowerPrim_matches (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (bounded : layout.Bounded dst) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) placement (Env.cons (prim.eval env) env)
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))).regs :=
  matched.setRegs bounded (prim.eval env) (primExpr_valueFits layout prim env entry hw matched fits)

/-- Existing-variable assignment updates exactly that mathematical binding and
preserves every other represented local. -/
theorem lowerAssign_matches (layout : RegisterMap Γ) (target : Var Γ τ) (value : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env value)
    (regular : layout.Regular) :
    RegisterMap.Matches layout placement (env.set target (value.eval env))
      (entry.setRegs (valueRegs τ (layout.base target)) (valueWords placement (value.eval env))).regs :=
  matched.set regular target (value.eval env)
    (primExpr_valueFits layout value env entry hw matched fits)

/-- Return materialization writes only the source result's actual fields. -/
theorem lowerReturn_safe (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env))
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount τ)) :
    Source.SafeExec program heapLimit depth (lowerReturn layout resultSlot atom) entry
      (entry.setRegs (valueRegs τ resultSlot) (valueWords placement (atom.eval env))) :=
  copyAtom_safe layout resultSlot atom env entry hw matched fits copySafe

/-- Returning into a separate result interval preserves the actual local
environment. This conditional frame fact adds no restriction to ordinary
return execution, whose scalar result is allowed to overlap source fields. -/
theorem lowerReturn_matches (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w)
    (matched : layout.Matches placement env entry.regs)
    (separated : layout.AvoidsRange resultSlot (fieldCount τ)) :
    RegisterMap.Matches layout placement env
      (entry.setRegs (valueRegs τ resultSlot) (valueWords placement (atom.eval env))).regs := by
  intro σ v i
  rw [Source.State.setRegs_ne entry (valueRegs τ resultSlot)
    (valueWords placement (atom.eval env)) (layout v i) (separated.not_mem v i)]
  exact matched v i

/-- Reading the result tuple after receiving its fields recovers those actual
fields, not a value selected from a specification. -/
theorem resultExprs_setRegs_eval (τ : Ty) (resultSlot : Reg) (value : Value τ)
    (entry : Source.State w) :
    (resultExprs τ resultSlot).map
        (entry.setRegs (valueRegs τ resultSlot) (valueWords placement value)).eval =
      valueWords placement value := by
  apply List.ext_getElem
  · simp only [List.length_map, resultExprs_length, valueWords_length]
  · intro i hi _
    have distinct : (valueRegs τ resultSlot).Nodup := by
      simpa only [valueRegs] using
        (List.nodup_range' (s := resultSlot) (n := fieldCount τ))
    have lengths : (valueRegs τ resultSlot).length = (valueWords placement value).length := by
      simp only [valueRegs_length, valueWords_length]
    have index : i < (valueRegs τ resultSlot).length := by
      simpa only [resultExprs, List.length_map] using hi
    simpa only [resultExprs, List.getElem_map, Source.State.eval, Expr.eval] using
      Source.State.setRegs_getElem entry (valueRegs τ resultSlot) (valueWords placement value)
        distinct lengths i index

/-- A native cell becomes exactly one field of its corresponding source value. -/
@[simp] theorem valueWords_cell (placement : Nat → Word w) (kind : CellTy)
    (value : CellValue kind) :
    valueWords placement (kind.toValue value) = [cellWord w value] := by
  cases kind <;>
    simp only [CellTy.toValue, valueWords_nat, valueWords_bool, cellWord, cellToNat]

/-- Source cell ranges agree with the ordinary scalar value representation. -/
theorem valueFits_cell_iff (kind : CellTy) (value : CellValue kind) :
    ValueFits w (kind.toValue value) ↔ cellToNat value < 2 ^ w := by
  cases kind <;> rfl

/-- A native cell has precisely one actual receiver. -/
@[simp] theorem valueRegs_cell (kind : CellTy) (dst : Reg) :
    valueRegs kind.toTy dst = [dst] := by
  cases kind <;> simp [CellTy.toTy, valueRegs]

/-- The first field of a borrowed view is its actual represented word address. -/
theorem bufferBase_eval (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind))
    (env : Env Γ) (entry : Source.State w) (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (buffer.eval env)) :
    entry.eval (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩) =
      (bufferRef placement (buffer.eval env)).base := by
  simpa only [valueField_buffer_zero, Word.ofNat_toNat_self, bufferRef] using
    atomFieldExpr_eval layout buffer env entry matched fits ⟨0, by change 0 < 2; decide⟩

/-- A lowered read executes the actual load and receives its native cell value.
The complete heap and its aliases remain represented at that same endpoint. -/
theorem lowerRead_safe (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (indexFits : ValueFits w (index.eval env))
    {cell : CellValue kind} (loaded : heap.read (buffer.eval env) (index.eval env) = .ok cell) :
    let received := entry.setRegs (valueRegs kind.toTy dst)
      (valueWords placement (kind.toValue cell))
    Source.SafeExec program heapLimit depth (lowerRead layout dst buffer index) entry received ∧
      HeapRep placement heapLimit heap received ∧ ValueFits w (kind.toValue cell) := by
  dsimp only
  obtain ⟨execution, _, preserved, fits⟩ := represented.read_assign
    (program := program) (depth := depth) (control := 0) loaded dst
    (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩) (atomExpr layout index .nat)
    (atomFieldExpr_readsBelow layout buffer ⟨0, by change 0 < 2; decide⟩ entry)
    (atomExpr_readsBelow layout index .nat entry)
    (bufferBase_eval layout buffer env entry matched bufferFits)
    (atomExpr_eval layout index .nat env entry hw matched indexFits)
  simpa only [lowerRead, valueRegs_cell, valueWords_cell, Source.State.setRegs_singleton] using
    And.intro execution (And.intro preserved ((valueFits_cell_iff kind cell).mpr fits))

/-- A lowered store uses the actual runtime view, index and scalar expression.
Its endpoint represents the updated shared heap, not a restored entry heap. -/
theorem lowerWrite_safe (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap finish : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (indexFits : ValueFits w (index.eval env))
    (valueFits : ValueFits w (value.eval env))
    (written : heap.write (buffer.eval env) (index.eval env)
      (kind.ofValue (value.eval env)) = .ok finish) :
    let updated := entry.setMem
      (arrayAddr (bufferRef placement (buffer.eval env)).base (index.eval env))
      (cellWord w (kind.ofValue (value.eval env)))
    Source.SafeExec program heapLimit depth (lowerWrite layout buffer index value) entry updated ∧
      HeapRep placement heapLimit finish updated := by
  dsimp only
  have fits : cellToNat (kind.ofValue (value.eval env)) < 2 ^ w := by
    cases kind <;> exact valueFits
  have stored : entry.eval (atomExpr layout value (Scalar.cell kind)) =
      cellWord w (kind.ofValue (value.eval env)) := by
    have observed := atomExpr_eval layout value (Scalar.cell kind) env entry hw matched valueFits
    cases kind <;> exact observed
  obtain ⟨execution, _, preserved⟩ := represented.write_store
    (program := program) (depth := depth) (control := 0) written fits
    (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩) (atomExpr layout index .nat)
    (atomExpr layout value (Scalar.cell kind))
    (atomFieldExpr_readsBelow layout buffer ⟨0, by change 0 < 2; decide⟩ entry)
    (atomExpr_readsBelow layout index .nat entry)
    (atomExpr_readsBelow layout value (Scalar.cell kind) entry)
    (bufferBase_eval layout buffer env entry matched bufferFits)
    (atomExpr_eval layout index .nat env entry hw matched indexFits) stored
  exact ⟨execution, preserved⟩

/-- Successful slicing computes its descriptor by word address addition and
the requested length. Empty endpoint views need no stronger address bound. -/
theorem bufferSlice_fields (placement : Nat → Word w) (buffer : Buffer kind)
    (offset length : Nat) {view : Buffer kind}
    (sliced : buffer.slice offset length = .ok view) :
    valueWords placement (τ := .buffer kind) view =
        [(bufferRef placement buffer).base + BitVec.ofNat w offset, BitVec.ofNat w length] ∧
      view.length = length := by
  by_cases span : offset + length ≤ buffer.length
  · have same := Except.ok.inj ((Buffer.slice_eq buffer span).symm.trans sliced)
    rw [← same, valueWords_buffer]
    refine ⟨?_, rfl⟩
    change [arrayAddr (placement buffer.object) (buffer.offset + offset), BitVec.ofNat w length] =
      [arrayAddr (arrayAddr (placement buffer.object) buffer.offset) offset, BitVec.ofNat w length]
    rw [arrayAddr_add]
  · simp [Buffer.slice, span] at sliced

/-- A slice executes two ordinary assignments into fresh fields. The second
expression is evaluated after the first assignment and is proved unchanged by
layout freshness; no simultaneous assignment or hidden descriptor construction
is used. The underlying objects and all aliases retain their actual heap. -/
theorem lowerSlice_safe (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (offset length : Atom Γ .nat) (env : Env Γ)
    (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    {heap : Complexity.Language.Heap} (represented : HeapRep placement heapLimit heap entry)
    (bufferFits : ValueFits w (buffer.eval env)) (offsetFits : ValueFits w (offset.eval env))
    (lengthFits : ValueFits w (length.eval env)) (bounded : layout.Bounded dst)
    {view : Buffer kind}
    (sliced : (buffer.eval env).slice (offset.eval env) (length.eval env) = .ok view) :
    let received := entry.setRegs (valueRegs (.buffer kind) dst)
      (valueWords placement (τ := .buffer kind) view)
    Source.SafeExec program heapLimit depth (lowerSlice layout dst buffer offset length)
        entry received ∧
      HeapRep placement heapLimit heap received ∧ ValueFits w (τ := .buffer kind) view := by
  dsimp only
  have fields := bufferSlice_fields placement (buffer.eval env) (offset.eval env)
    (length.eval env) sliced
  let baseWord := (bufferRef placement (buffer.eval env)).base + BitVec.ofNat w (offset.eval env)
  let middle := entry.setReg dst baseWord
  have baseEval : entry.eval (.bin .add (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩)
      (atomExpr layout offset .nat)) = baseWord := by
    change entry.eval (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩) +
      entry.eval (atomExpr layout offset .nat) = baseWord
    rw [bufferBase_eval layout buffer env entry matched bufferFits,
      atomExpr_eval layout offset .nat env entry hw matched offsetFits]
    all_goals rfl
  have first : Source.SafeExec program heapLimit depth
      (.assign dst (.bin .add (atomFieldExpr layout buffer ⟨0, by change 0 < 2; decide⟩)
        (atomExpr layout offset .nat))) entry middle := by
    change Source.SafeExec _ _ _ _ entry (entry.setReg dst baseWord)
    rw [← baseEval]
    exact .assign ⟨atomFieldExpr_readsBelow layout buffer ⟨0, by change 0 < 2; decide⟩ entry,
      atomExpr_readsBelow layout offset .nat entry⟩
  have matchedMiddle : layout.Matches placement env middle.regs := by
    intro τ v i
    change ((entry.setReg dst baseWord).regs (layout v i)).toNat = _
    rw [Source.State.setReg_ne entry dst (layout v i) baseWord (Nat.ne_of_lt (bounded v i))]
    exact matched v i
  have lengthEval : middle.eval (atomExpr layout length .nat) =
      BitVec.ofNat w (length.eval env) := by
    simpa only [Scalar.toNat] using
      atomExpr_eval layout length .nat env middle hw matchedMiddle lengthFits
  have second : Source.SafeExec program heapLimit depth
      (.assign (dst + 1) (atomExpr layout length .nat)) middle
      (middle.setReg (dst + 1) (BitVec.ofNat w (length.eval env))) := by
    rw [← lengthEval]
    exact .assign (atomExpr_readsBelow layout length .nat middle)
  refine ⟨?_, represented.setRegs _ _, ?_⟩
  · simpa only [lowerSlice, valueRegs_buffer, fields.1, Source.State.setRegs_cons,
      Source.State.setRegs_singleton] using Source.SafeExec.seq first second
  · change view.length < 2 ^ w
    rw [fields.2]
    exact lengthFits

end Ram.LanguageCompiler
