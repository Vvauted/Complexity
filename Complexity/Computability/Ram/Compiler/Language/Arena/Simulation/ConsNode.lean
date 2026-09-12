/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.MeasuredNode

/-!
# Immutable-node construction around allocating continuations

Node construction materializes the head and optional tail, runs the existing
three-word allocator and binds its fresh source reference. The continuation
runs at that same extended placement and cursor; it may allocate again.

Rooted input values justify sharing the old tail without a traversal. The
statement's readiness retains the real head/tag ranges and storage capacity;
no extra lifetime or time premise is added to the public launch interface.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth cursor finalCursor steps : Nat}

/-- Execute the actual node allocator before the same lexical continuation,
retaining both the newly allocated node and all original object placements. -/
theorem consNode {kind : CellTy} {head : Atom Γ kind.toTy}
    {tail : Atom Γ (.option (.node kind))}
    {continuation : Complexity.Language.Stmt signatures (.node kind :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {finish : Complexity.Language.State (.node kind :: Γ)} {outcome : Control result}
    {body : Complexity.Language.Exec program continuation
      (let allocated := entry.heap.cons (kind.ofValue (head.eval entry.locals))
        (tail.eval entry.locals)
       Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩) finish outcome}
    (headFits : ValueFits w (head.eval entry.locals))
    (tailFits : ValueFits w (tail.eval entry.locals))
    (capacity : cursor + 3 ≤ heapLimit)
    (bodyCore : ArenaCoreSimulates body w heapLimit depth (cursor + 3) finalCursor steps) :
    ArenaCoreSimulates (.consNode body) w heapLimit depth cursor finalCursor
      (consNodeCodeSize + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  let allocated := entry.heap.cons (kind.ofValue (head.eval entry.locals))
    (tail.eval entry.locals)
  let allocatedPlacement := Function.update placement entry.heap.objects.size (BitVec.ofNat w cursor)
  obtain ⟨middle, first, middleArena, matching, frame⟩ :=
    lowerConsNode_measured (control := controlReg) (program := lowerProgram program)
      (depth := depth) layout next head tail entry.locals s arena rooted matched bounded
      headFits tailFits capacity
  have growth : entry.heap.ShapeExtends allocated.2 :=
    entry.heap.shapeExtends_cons _ _
  have bodyRooted : (Env.cons (τ := .node kind) allocated.1 entry.locals).Rooted allocated.2 :=
    Env.Rooted.cons (τ := .node kind) (Env.Rooted.mono rooted growth)
      allocated.1 (Heap.node_lt_size (entry.heap.node?_cons_new
        (kind.ofValue (head.eval entry.locals)) (tail.eval entry.locals)))
  have bodyBounded :
      RegisterMap.Bounded (RegisterMap.extend layout (.node kind) next) (next + 4) := by
    intro τ v i
    exact Nat.lt_of_lt_of_le (RegisterMap.extend_bounded (τ := .node kind) bounded v i)
      (by simp only [fieldCount]; omega)
  have flagPreserved : middle.regs flag = 0 := (frame flag (Or.inl fresh)).trans flagZero
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw allocatedPlacement (RegisterMap.extend layout (.node kind) next)
      (next + 4) resultSlot flag middle
      (regular.extend bounded) bodyBounded matching
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
