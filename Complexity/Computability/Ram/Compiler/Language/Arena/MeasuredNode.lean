/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Frame
import Complexity.Computability.Ram.Compiler.Language.Arena.NodeExecution
import Complexity.Computability.Ram.Compiler.Language.MeasuredNode
import Complexity.Computability.Ram.Compiler.Language.Placement

/-!
# Measured inline allocation of a typed immutable node

Three actual field copies prepare the head, optional-tail tag and placed tail
address. The existing allocator then reserves and initializes one three-word
node. The same counted execution supplies the final arena, fresh reference and
lexical correspondence under the extended placement.

Only the optional tail's existing root is needed. There is no runtime validation
or copying of its suffix, and a mathematical List observation is not required
by this raw node operation. Existing locals retain their representation through
their rootedness; the four fresh local slots account for operand preparation
as well as the returned base.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Materialize the actual operands and allocate one immutable node. The result
and complete arena belong to the same execution, including all three copies and
initialization stores. Only four fresh local slots may change. -/
theorem lowerConsNode_measured
    {w control heapLimit depth cursor : Nat} {program : Ram.Program}
    {Γ : List Ty} {kind : CellTy} {placement : Nat → Word w}
    {heap : Complexity.Language.Heap}
    (layout : RegisterMap Γ) (next : Reg) (head : Atom Γ kind.toTy)
    (tail : Atom Γ (.option (.node kind))) (env : Env Γ) (entry : Source.State w)
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (rooted : env.Rooted heap) (matched : layout.Matches placement env entry.regs)
    (bounded : layout.Bounded next) (headFits : ValueFits w (head.eval env))
    (tailFits : ValueFits w (tail.eval env)) (capacity : cursor + 3 ≤ heapLimit) :
    let allocated := heap.cons (kind.ofValue (head.eval env)) (tail.eval env)
    let finalPlacement := Function.update placement heap.objects.size (BitVec.ofNat w cursor)
    ∃ finish, Source.LocalMeasuredExec control program heapLimit depth
        (lowerConsNode layout next head tail) consNodeCodeSize entry finish ∧
      ArenaRep finalPlacement (cursor + 3) heapLimit allocated.2 finish ∧
      RegisterMap.Matches (RegisterMap.extend layout (.node kind) next) finalPlacement
        (Env.cons allocated.1 env) finish.regs ∧
      ∀ slot, slot < next ∨ next + 4 ≤ slot → finish.regs slot = entry.regs slot := by
  dsimp only
  have hw : 0 < w := by
    have cursorFits := lt_of_le_of_lt arena.cursor_le arena.limit_lt
    have positive := arena.cursor_pos
    by_contra notPositive
    have width : w = 0 := by omega
    simp only [width, Nat.pow_zero] at cursorFits
    omega
  have cellFits : cellToNat (kind.ofValue (head.eval env)) < 2 ^ w := by
    cases kind <;> exact headFits
  let exprs := atomExprs layout head ++ atomExprs layout tail
  let words := [cellWord w (kind.ofValue (head.eval env)),
    if (tail.eval env).isSome then 1 else 0,
    (tail.eval env).elim 0 (fun ref => placement ref.object)]
  let slots := [next + 1, next + 2, next + 3]
  let operands := entry.setRegs slots words
  have exprCount : exprs.length = 3 := by
    dsimp only [exprs]
    rw [List.length_append, atomExprs_length, atomExprs_length]
    cases kind <;> rfl
  have exprValues : exprs.map entry.eval = words := by
    dsimp only [exprs]
    rw [List.map_append, atomExprs_eval layout head env entry hw matched headFits,
      atomExprs_eval layout tail env entry hw matched tailFits]
    have encoded :=
      valueWords_node_fields placement kind (kind.ofValue (head.eval env)) (tail.eval env)
    rw [valueWords_prod (α := kind.toTy) (β := .option (.node kind))] at encoded
    simpa only [CellTy.toValue_ofValue] using encoded
  have reads : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem := by
    intro expr member
    rcases List.mem_append.mp member with member | member
    · exact atomExprs_readsBelow layout head entry expr member
    · exact atomExprs_readsBelow layout tail entry expr member
  have avoids : layout.AvoidsRange (next + 1) exprs.length := by
    intro τ v index
    exact Or.inl ((bounded v index).trans (Nat.lt_succ_self next))
  have separated : ∀ expr ∈ exprs, expr.AvoidsRange (next + 1) exprs.length := by
    intro expr member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact atomFieldExpr_avoidsRange layout head index avoids
    · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      exact atomFieldExpr_avoidsRange layout tail index avoids
  have prepared : Source.LocalMeasuredExec control program heapLimit depth
      (copyFields (next + 1) exprs)
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (copyFields (next + 1) exprs)) entry operands := by
    have execution := copyFields_localMeasured entry (next + 1) exprs reads (Or.inr separated)
      (control := control) (program := program) (depth := depth)
    rw [exprCount, exprValues] at execution
    exact execution
  have headReg : operands.regs (Source.Arena.Node.inlineRegisters next).head =
      cellWord w (kind.ofValue (head.eval env)) := by
    simp [operands, slots, words, Source.Arena.Node.inlineRegisters,
      Source.State.setRegs_cons, Source.State.setReg]
  have tagReg : operands.regs (Source.Arena.Node.inlineRegisters next).tag =
      (if (tail.eval env).isSome then 1 else 0) := by
    simp [operands, slots, words, Source.Arena.Node.inlineRegisters,
      Source.State.setRegs_cons, Source.State.setReg]
  have tailReg : operands.regs (Source.Arena.Node.inlineRegisters next).tail =
      (tail.eval env).elim 0 (fun ref => placement ref.object) := by
    simp [operands, slots, words, Source.Arena.Node.inlineRegisters,
      Source.State.setRegs_cons, Source.State.setReg]
  obtain ⟨finish, allocation, post, represented, returned⟩ :=
    ArenaRep.cons_measured_of_rooted (program := program) (control := control) (depth := depth)
      (Source.Arena.Node.inlineRegisters next) (arena.setRegs slots words)
      (τ := kind) (head := kind.ofValue (head.eval env)) (tail := tail.eval env)
      (tail.eval_rooted rooted) cellFits capacity headReg tagReg tailReg
  have execution : Source.LocalMeasuredExec control program heapLimit depth
      (lowerConsNode layout next head tail) consNodeCodeSize entry finish := by
    rw [← lowerConsNode_stmtSize control (LocalCompiler.calleeLocals program) layout next head tail]
    simpa only [lowerConsNode, LocalCompiler.stmtSize_seq] using
      Source.LocalMeasuredExec.seq prepared allocation
  have frame : ∀ slot, slot < next ∨ next + 4 ≤ slot →
      finish.regs slot = entry.regs slot := by
    intro slot outside
    have different : slot ≠ (Source.Arena.Node.inlineRegisters next).base := by
      change slot ≠ next
      rcases outside with before | after
      · exact Nat.ne_of_lt before
      · exact Nat.ne_of_gt
          (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 4)) after)
    have notOperand : slot ∉ slots := by
      have separated (offset : Nat) (bound : offset < 4) : slot ≠ next + offset := by
        rcases outside with before | after
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le before (Nat.le_add_right next offset))
        · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left bound next) after)
      simp [slots, separated 1 (by decide), separated 2 (by decide), separated 3 (by decide)]
    exact (post.other slot different).trans (Source.State.setRegs_ne entry slots words slot notOperand)
  refine ⟨finish, execution, represented, ?_, frame⟩
  have agreed := Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
    (BitVec.ofNat w cursor)
  apply RegisterMap.Matches.extend (matched.placement agreed rooted)
  · intro τ v index
    exact frame _ (Or.inl (bounded v index))
  · intro index
    have zero : index.val = 0 := Nat.lt_one_iff.mp index.isLt
    simpa only [valueField_node, zero, Nat.add_zero, Source.Arena.Node.inlineRegisters] using
      congrArg (fun word : Word w => word.toNat) returned

end Ram.LanguageCompiler
