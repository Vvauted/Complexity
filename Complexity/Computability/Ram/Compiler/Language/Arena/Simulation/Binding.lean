/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.MeasuredAllocation
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues

/-!
# Lexical binding and fresh allocation in counted compilation

Both rules consume a simulation of the actual lexical continuation. Allocation
extends the placement only at the new object identifier and passes the actual
initialized memory and advanced cursor onward. Leaving the lexical scope does
not reclaim an object or reset the cursor.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth cursor finalCursor steps : Nat}

/-- Binding a primitive composes its existing counted implementation with the
same source continuation, retaining all allocation effects of that continuation. -/
theorem letPrim {τ : Ty} {value : Prim Γ τ}
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
    {outcome : Control result}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons (value.eval entry.locals) entry) finish outcome}
    (fits : PrimFits w entry.locals value)
    (bodyCore : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps) :
    ArenaCoreSimulates (.letPrim body) w heapLimit depth cursor finalCursor
      (primCodeSize value + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  have first := lowerPrim_measured (control := controlReg) (program := lowerProgram program)
    (heapLimit := heapLimit) (depth := depth) layout next value entry.locals s hw matched fits
    (Or.inr (bounded.avoidsRange _))
  have matching : RegisterMap.Matches (RegisterMap.extend layout τ next) placement
      (Env.cons (value.eval entry.locals) entry.locals)
      (s.setRegs (valueRegs τ next) (valueWords placement (value.eval entry.locals))).regs :=
    lowerPrim_matches layout next value entry.locals s hw matched fits bounded
  have bodyRooted : (Env.cons (value.eval entry.locals) entry.locals).Rooted entry.heap :=
    Env.Rooted.cons rooted _ (value.eval_rooted rooted)
  have flagPreserved := (valueRegs_setRegs_other s τ next flag
    (valueWords placement (value.eval entry.locals))
    (flag_not_mem_valueRegs_of_lt τ next flag fresh)).trans flagZero
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw placement (RegisterMap.extend layout τ next)
      (next + fieldCount τ) resultSlot flag _
      (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching
      (RegisterMap.Avoids.extend avoids fresh)
      (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
      (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
      bodyRooted (arena.setRegs _ _) flagPreserved
  refine ⟨finalPlacement, t, .seq first rest, ControlMatches.tail property,
    finalArena, agreed, ?_⟩
  intro separate
  exact RegisterMap.Matches.tail (finalMatches (separate.extend
    (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

/-- Fresh typed allocation uses the actual initialized inline allocator, then
threads its placement and reserved extent through the lexical continuation. -/
theorem alloc {kind : CellTy} {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {finish : Complexity.Language.State (.buffer kind :: Γ)} {outcome : Control result}
    {body : Complexity.Language.Exec program continuation
      (let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
        (kind.ofValue (initial.eval entry.locals))
       Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩) finish outcome}
    (initialFits : ValueFits w (initial.eval entry.locals))
    (capacity : cursor + length.eval entry.locals ≤ heapLimit)
    (bodyCore : ArenaCoreSimulates body w heapLimit depth
      (cursor + length.eval entry.locals) finalCursor steps) :
    ArenaCoreSimulates (.alloc body) w heapLimit depth cursor finalCursor
      (14 * length.eval entry.locals + 18 + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
    (kind.ofValue (initial.eval entry.locals))
  let allocatedPlacement := Function.update placement entry.heap.objects.size (BitVec.ofNat w cursor)
  obtain ⟨middle, first, middleArena, matching, frame⟩ :=
    lowerAlloc_measured (control := controlReg) (program := lowerProgram program)
      (depth := depth) layout next length initial entry.locals s arena rooted matched bounded
      initialFits capacity
  have growth : entry.heap.ShapeExtends allocated.2 :=
    entry.heap.shapeExtends_alloc _ _
  have bodyRooted : (Env.cons (τ := .buffer kind) allocated.1 entry.locals).Rooted allocated.2 :=
    Env.Rooted.cons (τ := .buffer kind) (Env.Rooted.mono rooted growth)
      allocated.1 (entry.heap.alloc_rooted _ _)
  have flagPreserved : middle.regs flag = 0 := (frame flag (Or.inl fresh)).trans flagZero
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw allocatedPlacement (RegisterMap.extend layout (.buffer kind) next)
      (next + fieldCount (.buffer kind)) resultSlot flag middle
      (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching
      (RegisterMap.Avoids.extend avoids fresh)
      (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
      (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
      bodyRooted middleArena flagPreserved
  have allocatedAgreement : Placement.Agrees entry.heap placement allocatedPlacement :=
    Placement.agrees_update entry.heap placement (Nat.le_refl _) (BitVec.ofNat w cursor)
  refine ⟨finalPlacement, t, .seq first rest, ControlMatches.tail property,
    finalArena, allocatedAgreement.trans_of_shape agreed growth, ?_⟩
  intro separate
  exact RegisterMap.Matches.tail (finalMatches (separate.extend
    (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

end Ram.LanguageCompiler.ArenaCoreSimulates
