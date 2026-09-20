/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Values.Basic
import Complexity.Computability.Ram.Compiler.Language.Copy

/-!
# Copying lowered values and bindings

Primitive binding, assignment and return materialization execute actual
sequential field copies. Separation preserves still-live operands; singleton
copies and assignment to a variable's own fields retain their supported aliasing.
The resulting register correspondence describes the same source values and
lexical updates, without an instruction budget or heap traversal.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {placement : Nat → Word w}

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

end Ram.LanguageCompiler
