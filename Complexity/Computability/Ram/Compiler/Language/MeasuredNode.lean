/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.CodeSize
import Complexity.Computability.Ram.Compiler.Language.Heap.NodeExecution
import Complexity.Computability.Ram.Compiler.Language.Values

/-!
# Measured execution of typed node reads

The source node-read primitive receives its actual scalar head and optional
tail in three fresh fields. It reuses the existing three-load block and complete
heap representation. The same endpoint supplies the lexical binding, all memory
and stream frames, and the exact emitted instruction count.

The source object number is never truncated to a word or recovered from a stored
address. The complete heap representation already supplies the head and tag
ranges; no extra word-range premise or runtime tail-validation scan is needed.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

variable {placement : Nat → Word w} {control : Nat}

/-- A node read returns the same three words as the source pair encoding. -/
theorem valueWords_node_fields (placement : Nat → Word w) (kind : CellTy)
    (head : CellValue kind) (tail : Option (NodeRef kind)) :
    valueWords placement (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) =
      [cellWord w head, if tail.isSome then 1 else 0,
        tail.elim 0 (fun ref => placement ref.object)] := by
  rw [valueWords_prod (α := kind.toTy) (β := .option (.node kind)),
    valueWords_cell placement kind head]
  cases tail with
  | none =>
      rw [valueWords_none placement (.node kind)]
      rfl
  | some tail =>
      rw [valueWords_some (τ := .node kind), valueWords_node]
      rfl

/-- The returned head, tag and tail occupy three consecutive lexical fields. -/
theorem valueRegs_node_fields (kind : CellTy) (dst : Reg) :
    valueRegs (.prod kind.toTy (.option (.node kind))) dst =
      [dst, dst + 1, dst + 2] := by
  cases kind <;> rfl

/-- A successful represented lookup supplies the exact ranges of the returned
pair, including the optional tail's tag. Source identifiers have no word bound. -/
theorem HeapRep.node_valueFits {heap : Heap} {entry : Source.State w}
    (represented : HeapRep placement heapLimit heap entry)
    {kind : CellTy} {object : Nat} {head : CellValue kind} {tail : Option (NodeRef kind)}
    (found : heap.node? kind object = some (head, tail)) :
    ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail) := by
  have fits := represented.fit (Heap.node?_eq_some_iff.mp found)
  refine ⟨(valueFits_cell_iff kind head).mpr fits.1, ?_⟩
  cases tail with
  | none => trivial
  | some tail => exact ⟨fits.2, True.intro⟩

/-- Execute the actual three loads and receive their typed pair. All heap
objects remain represented at this same endpoint, including shared tails. -/
theorem lowerReadNode_measured (layout : RegisterMap Γ) (dst : Reg)
    (ref : Atom Γ (.node kind)) (env : Env Γ) (entry : Source.State w)
    (matched : layout.Matches placement env entry.regs)
    {heap : Heap} (represented : HeapRep placement heapLimit heap entry)
    (bounded : layout.Bounded dst)
    {head : CellValue kind} {tail : Option (NodeRef kind)}
    (found : heap.node? kind (ref.eval env).object = some (head, tail)) :
    let received := entry.setRegs (valueRegs (.prod kind.toTy (.option (.node kind))) dst)
      (valueWords placement (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail))
    Source.LocalMeasuredExec control program heapLimit depth (lowerReadNode layout dst ref)
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (lowerReadNode layout dst ref)) entry received ∧
      HeapRep placement heapLimit heap received ∧
      ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) := by
  dsimp only
  cases ref with
  | var ref =>
      change heap.node? kind (env.get ref).object = some (head, tail) at found
      have baseBound := bounded ref ⟨0, Nat.zero_lt_one⟩
      let r : Source.Node.Registers :=
        { base := layout ref ⟨0, Nat.zero_lt_one⟩
          head := dst
          tag := dst + 1
          tail := dst + 2
          base_ne_head := Nat.ne_of_lt baseBound
          base_ne_tag := Nat.ne_of_lt (Nat.lt_trans baseBound (Nat.lt_succ_self dst))
          head_ne_tag := Nat.ne_of_lt (Nat.lt_succ_self dst)
          head_ne_tail := Nat.ne_of_lt
            (Nat.lt_trans (Nat.lt_succ_self dst) (Nat.lt_succ_self (dst + 1)))
          tag_ne_tail := Nat.ne_of_lt (Nat.lt_succ_self (dst + 1)) }
      have base : entry.regs r.base = placement (env.get ref).object := by
        apply BitVec.eq_of_toNat_eq
        exact matched ref ⟨0, Nat.zero_lt_one⟩
      have fields := represented.node_fields found
      have endpoint : r.loaded entry =
          entry.setRegs (valueRegs (.prod kind.toTy (.option (.node kind))) dst)
            (valueWords placement (τ := .prod kind.toTy (.option (.node kind)))
              (kind.toValue head, tail)) := by
        unfold Source.Node.Registers.loaded
        rw [base, fields.1, fields.2.1, fields.2.2]
        rw [valueRegs_node_fields, valueWords_node_fields]
        rfl
      obtain ⟨execution, _, preserved, _⟩ := represented.node_read r
        (program := program) (control := control) (depth := depth)
        (ref := env.get ref) found base
      rw [endpoint] at execution preserved
      exact ⟨execution, preserved, represented.node_valueFits found⟩

end Ram.LanguageCompiler
