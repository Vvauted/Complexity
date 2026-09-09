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

/-- A primitive executes its assignments or actual sequential field copy and
produces its encoded fields. This theorem does not assume a time budget. -/
theorem lowerPrim_safe (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange dst (fieldCount τ)) :
    Source.SafeExec program heapLimit depth (lowerPrim layout dst prim) entry
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))) := by
  cases τ with
  | nat =>
      change Source.SafeExec _ _ _ (.assign dst (primExpr layout prim .nat)) entry
        (entry.setReg dst (BitVec.ofNat w (Scalar.toNat .nat (prim.eval env))))
      rw [← primExpr_eval layout prim .nat env entry hw matched fits]
      exact .assign (primExpr_readsBelow layout prim .nat entry)
  | bool =>
      change Source.SafeExec _ _ _ (.assign dst (primExpr layout prim .bool)) entry
        (entry.setReg dst (BitVec.ofNat w (Scalar.toNat .bool (prim.eval env))))
      rw [← primExpr_eval layout prim .bool env entry hw matched fits]
      exact .assign (primExpr_readsBelow layout prim .bool entry)
  | unit => exact .skip
  | buffer kind =>
      cases prim with
      | atom atom => exact copyAtom_safe layout dst atom env entry hw matched fits copySafe

/-- A realized primitive's actual result satisfies the source value range
condition, including a buffer's length rather than a fictitious scalar handle. -/
theorem primExpr_valueFits (layout : RegisterMap Γ) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim) :
    ValueFits w (prim.eval env) := by
  have scalarFits (scalar : Scalar τ) : scalar.toNat (prim.eval env) < 2 ^ w := by
    have observed := primExpr_toNat layout prim scalar env entry.regs entry.mem hw matched fits
    exact observed ▸ (entry.eval (primExpr layout prim scalar)).isLt
  cases τ with
  | nat => exact (Scalar.fits_iff .nat (prim.eval env)).mpr (scalarFits .nat)
  | bool => exact (Scalar.fits_iff .bool (prim.eval env)).mpr (scalarFits .bool)
  | unit => trivial
  | buffer kind => cases prim with
      | atom atom => exact fits

/-- Fresh primitive binding extends the existing environment correspondence. -/
theorem lowerPrim_matches (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs) (fits : PrimFits w env prim)
    (bounded : layout.Bounded dst) :
    RegisterMap.Matches (RegisterMap.extend layout τ dst) placement (Env.cons (prim.eval env) env)
      (entry.setRegs (valueRegs τ dst) (valueWords placement (prim.eval env))).regs :=
  matched.setRegs bounded (prim.eval env) (primExpr_valueFits layout prim env entry hw matched fits)

/-- Return materialization writes only the source result's actual fields. -/
theorem lowerReturn_safe (layout : RegisterMap Γ) (resultSlot : Reg) (atom : Atom Γ τ)
    (env : Env Γ) (entry : Source.State w) (hw : 0 < w)
    (matched : layout.Matches placement env entry.regs)
    (fits : ValueFits w (atom.eval env))
    (copySafe : fieldCount τ ≤ 1 ∨ layout.AvoidsRange resultSlot (fieldCount τ)) :
    Source.SafeExec program heapLimit depth (lowerReturn layout resultSlot atom) entry
      (entry.setRegs (valueRegs τ resultSlot) (valueWords placement (atom.eval env))) :=
  copyAtom_safe layout resultSlot atom env entry hw matched fits copySafe

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
