/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.MeasuredNode

/-!
# Node reads around allocating continuations

A successful typed lookup binds the head and actual optional tail through the
existing three-load lowering. The read changes registers only. Its continuation
may allocate and returns its actual final heap, cursor and extended placement.

The complete represented heap supplies backward links, so an exposed tail is
already rooted. This does not validate the tail's node kind or traverse it, and
imposes no additional premise on the caller's launch interface.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth cursor finalCursor steps : Nat}

/-- Bind the same three-word node result before an allocation-aware continuation.
All original roots keep their placements, including the newly exposed shared tail. -/
theorem readNode {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {finish : Complexity.Language.State (.prod kind.toTy (.option (.node kind)) :: Γ)}
    {outcome : Control result} {head : CellValue kind} {tail : Option (NodeRef kind)}
    {found : entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail)}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) entry) finish outcome}
    (bodyCore : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps)
    (valueFits : ValueFits w (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail)) :
    ArenaCoreSimulates (.readNode found body) w heapLimit depth cursor finalCursor
      (readNodeCodeSize + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨first, _, _⟩ := lowerReadNode_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout next ref entry.locals s matched arena.heapRep bounded found
  rw [lowerReadNode_stmtSize] at first
  have matching : RegisterMap.Matches
      (RegisterMap.extend layout (.prod kind.toTy (.option (.node kind))) next) placement
      (Env.cons (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) entry.locals)
      (s.setRegs (valueRegs (.prod kind.toTy (.option (.node kind))) next)
        (valueWords placement (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail))).regs :=
    matched.setRegs (τ := .prod kind.toTy (.option (.node kind))) bounded
      (kind.toValue head, tail) valueFits
  have flagPreserved := (valueRegs_setRegs_other s
    (.prod kind.toTy (.option (.node kind))) next flag
    (valueWords placement (τ := .prod kind.toTy (.option (.node kind)))
      (kind.toValue head, tail))
    (flag_not_mem_valueRegs_of_lt (.prod kind.toTy (.option (.node kind))) next flag fresh)).trans
      flagZero
  have tailRooted : ValueRooted entry.heap (τ := .option (.node kind)) tail := by
    cases tail with
    | none => trivial
    | some tail => exact arena.heapRep.node_backward.node_tail_lt_size found
  have continuationRooted :
      (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) entry).locals.Rooted entry.heap :=
    Env.Rooted.cons (τ := .prod kind.toTy (.option (.node kind))) rooted
      (kind.toValue head, tail) ⟨CellTy.toValue_rooted entry.heap kind head, tailRooted⟩
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw placement
      (RegisterMap.extend layout (.prod kind.toTy (.option (.node kind))) next)
      (next + fieldCount (.prod kind.toTy (.option (.node kind)))) resultSlot flag _
      (regular.extend bounded) (RegisterMap.extend_bounded bounded) matching
      (RegisterMap.Avoids.extend avoids fresh)
      (Nat.lt_of_lt_of_le fresh (Nat.le_add_right _ _)) resultFlag
      (copySafe_extend copySafe (Nat.le_trans resultFlag (Nat.le_of_lt fresh)))
      continuationRooted (arena.setRegs _ _) flagPreserved
  refine ⟨finalPlacement, t, Source.LocalMeasuredExec.seq first rest,
    ControlMatches.tail property, finalArena, agreed, ?_⟩
  intro separate
  exact RegisterMap.Matches.tail (finalMatches (separate.extend
    (Nat.le_trans resultFlag (Nat.le_of_lt fresh))))

end Ram.LanguageCompiler.ArenaCoreSimulates
