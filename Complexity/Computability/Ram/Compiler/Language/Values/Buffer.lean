/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Values.Basic
import Complexity.Computability.Ram.Compiler.Language.HeapOperation

/-!
# Executing lowered buffer operations

Source cells and borrowed views use their actual word fields. Successful reads
and writes execute ordinary RAM loads and stores while preserving representation
of the same shared heap, including aliases. Slicing executes two assignments
and preserves the underlying objects; it neither allocates nor copies contents.

These operation rules require the actual source success and representation
conditions. They do not introduce runtime validation or simultaneous assignment.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {placement : Nat → Word w}

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
