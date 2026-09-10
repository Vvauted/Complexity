/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Allocation
import Complexity.Computability.Ram.Compiler.Language.Arena.Lowering
import Complexity.Computability.Ram.Compiler.Language.Values
import Complexity.Computability.Ram.Memory.Arena.Registers.Allocation

/-!
# Measured inline allocation of a typed source object

Two actual assignments materialize the source operands before the shared
allocator reserves and initializes storage. Its existing measured execution
therefore takes `14 * length + 18` instructions, including both assignments.
The same final memory represents `Heap.alloc`, and its returned descriptor
extends the caller's lexical environment under the extended placement.

This local compiler connection supplies the allocation case of the general
simulation in `Arena.MeasuredSimulation`. Capacity and exact initial values
remain backend preconditions; a time budget is not used to establish source
correctness or termination.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Initialize a fresh typed source object with the inline allocator's actual
execution and instruction count. Only the five selected local slots may change;
old rooted values retain their representation after placement extension. -/
theorem lowerAlloc_measured
    {w control heapLimit depth cursor : Nat} {program : Ram.Program}
    {Γ : List Ty} {kind : CellTy} {placement : Nat → Word w}
    {heap : Complexity.Language.Heap}
    (layout : RegisterMap Γ) (next : Reg) (length : Atom Γ .nat)
    (initial : Atom Γ kind.toTy) (env : Env Γ) (entry : Source.State w)
    (arena : ArenaRep placement cursor heapLimit heap entry)
    (rooted : env.Rooted heap) (matched : layout.Matches placement env entry.regs)
    (bounded : layout.Bounded next) (initialFits : ValueFits w (initial.eval env))
    (capacity : cursor + length.eval env ≤ heapLimit) :
    let allocated := heap.alloc (length.eval env) (kind.ofValue (initial.eval env))
    let finalPlacement := Function.update placement heap.objects.size (BitVec.ofNat w cursor)
    ∃ finish, Source.LocalMeasuredExec control program heapLimit depth
        (lowerAlloc layout next length initial) (14 * length.eval env + 18) entry finish ∧
      ArenaRep finalPlacement (cursor + length.eval env) heapLimit allocated.2 finish ∧
      RegisterMap.Matches (RegisterMap.extend layout (.buffer kind) next) finalPlacement
        (Env.cons allocated.1 env) finish.regs ∧
      ∀ slot, slot < next ∨ next + 5 ≤ slot → finish.regs slot = entry.regs slot := by
  dsimp only
  have cursorFits := lt_of_le_of_lt arena.cursor_le arena.limit_lt
  have exactBase : (BitVec.ofNat w cursor).toNat = cursor :=
    Word.ofNat_toNat_of_lt cursorFits
  have lengthFits : ValueFits w (length.eval env) := by
    change length.eval env < 2 ^ w
    exact lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left _ _) capacity) arena.limit_lt
  have hw : 0 < w := by
    by_contra zero
    have width : w = 0 := by omega
    have positive := arena.cursor_pos
    simp only [width, Nat.pow_zero] at cursorFits
    omega
  have cellFits : cellToNat (kind.ofValue (initial.eval env)) < 2 ^ w := by
    cases kind <;> exact initialFits
  let middle := entry.setReg (next + 1) (BitVec.ofNat w (length.eval env))
  let operands := middle.setReg (next + 2) (cellWord w (kind.ofValue (initial.eval env)))
  have lengthEval : entry.eval (atomExpr layout length .nat) =
      BitVec.ofNat w (length.eval env) := by
    simpa only [Scalar.toNat] using
      atomExpr_eval layout length .nat env entry hw matched lengthFits
  have first : Source.LocalMeasuredExec control program heapLimit depth
      (.assign (next + 1) (atomExpr layout length .nat)) 2 entry middle := by
    simpa only [LocalCompiler.stmtSize_assign, atomExpr_compile_length, lengthEval] using
      (Source.LocalMeasuredExec.assign (control := control) (program := program)
        (d := depth) (dst := next + 1) (atomExpr_readsBelow layout length .nat entry))
  have matchedMiddle : layout.Matches placement env middle.regs := by
    intro τ v i
    change ((entry.setReg (next + 1) _).regs (layout v i)).toNat = _
    rw [Source.State.setReg_ne entry (next + 1) (layout v i) _
      (Nat.ne_of_lt ((bounded v i).trans_le (Nat.le_add_right next 1)))]
    exact matched v i
  have initialEval : middle.eval (atomExpr layout initial (Scalar.cell kind)) =
      cellWord w (kind.ofValue (initial.eval env)) := by
    have observed := atomExpr_eval layout initial (Scalar.cell kind) env middle hw
      matchedMiddle initialFits
    cases kind <;> exact observed
  have second : Source.LocalMeasuredExec control program heapLimit depth
      (.assign (next + 2) (atomExpr layout initial (Scalar.cell kind))) 2 middle operands := by
    simpa only [LocalCompiler.stmtSize_assign, atomExpr_compile_length, initialEval] using
      (Source.LocalMeasuredExec.assign (control := control) (program := program)
        (d := depth) (dst := next + 2)
        (atomExpr_readsBelow layout initial (Scalar.cell kind) middle))
  have lengthReg : (operands.regs (next + 1)).toNat = length.eval env := by
    dsimp only [operands, middle]
    rw [Source.State.setReg_ne _ _ _ _ (by simp), Source.State.setReg_same,
      Word.ofNat_toNat_of_lt lengthFits]
  have pre : (Source.Arena.inlineRegisters next).Pre heapLimit (BitVec.ofNat w cursor)
      (length.eval env) (cellWord w (kind.ofValue (initial.eval env))) operands := by
    refine ⟨arena.cursor_eq, lengthReg, ?_, ?_, ?_, arena.limit_lt⟩
    · exact Source.State.setReg_same middle (next + 2) _
    · rw [exactBase]
      exact arena.cursor_pos
    · simpa only [exactBase] using capacity
  obtain ⟨finish, allocation, post⟩ :=
    (Source.Arena.inlineRegisters next).allocate_measured
      (program := program) (control := control) (depth := depth) pre
  have execution : Source.LocalMeasuredExec control program heapLimit depth
      (lowerAlloc layout next length initial) (14 * length.eval env + 18) entry finish := by
    have count : 2 + (2 + (14 * length.eval env + 14)) = 14 * length.eval env + 18 := by
      exact (Nat.add_assoc 2 2 (14 * length.eval env + 14)).symm.trans
        (Nat.add_left_comm 4 (14 * length.eval env) 14)
    simpa only [lowerAlloc, count] using Source.LocalMeasuredExec.seq first
      (Source.LocalMeasuredExec.seq second allocation)
  have frame : ∀ slot, slot < next ∨ next + 5 ≤ slot →
      finish.regs slot = entry.regs slot :=
    fun _ outside => lowerAlloc_regs_eq execution.erase outside
  have represented := arena.alloc cellFits capacity
    (by simpa only [arrayAddr, BitVec.ofNat_add_ofNat] using post.cursor)
    (by simpa only [objectWords, Array.map_replicate, Array.toList_replicate] using post.array)
    (by
      intro address positive below
      apply post.frame address
      · intro zero
        simp [zero] at positive
      · exact Or.inl (by simpa only [exactBase] using below))
  refine ⟨finish, execution, represented, ?_, frame⟩
  have agreed := Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
    (BitVec.ofNat w cursor)
  apply RegisterMap.Matches.extend (matched.placement agreed rooted)
  · intro τ v i
    exact frame _ (Or.inl (bounded v i))
  · intro i
    by_cases zero : i.val = 0
    · have baseReturned : finish.regs next = BitVec.ofNat w cursor := post.base_reg
      simpa [valueField, zero, Complexity.Language.Heap.alloc, arrayAddr] using
        congrArg (fun word : Word w => word.toNat) baseReturned
    · have one : i.val = 1 := by
        have bound := i.isLt
        change i.val < 2 at bound
        omega
      have lengthReturned : (finish.regs (next + 1)).toNat = length.eval env := by
        change (finish.regs (Source.Arena.inlineRegisters next).length).toNat = _
        rw [post.length_reg]
        exact lengthReg
      simpa only [valueField, one, Nat.one_ne_zero, if_false,
        Complexity.Language.Heap.alloc_length] using lengthReturned

end Ram.LanguageCompiler
