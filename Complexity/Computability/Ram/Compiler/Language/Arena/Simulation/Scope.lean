/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.Arena.Restriction
import Complexity.Computability.Ram.Compiler.Language.Effects
import Complexity.Computability.Ram.Memory.Arena.Scope

/-!
# Counted simulation of non-escaping allocation scopes

A fresh local saves the actual entry cursor. The existing body simulation runs
above that register, and its ordinary register frame protects the saved word.
Release runs after the body even when the source control is a return.

Only metadata is restored. Restriction keeps the final contents of pre-existing
objects, including writes through aliases; the source scope's non-escape proof
justifies discarding fresh object identities. The two real metadata operations
add six instructions to the same body's measured execution.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

/-- A scope saves and restores its cursor around the actual body execution.
The saved slot is protected by the shared lowering frame, not an additional
author-supplied register assumption. Returned fields and final locals survive
release unchanged, and old objects retain their current written contents. -/
theorem scope {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {w heapLimit depth cursor bodyCursor steps : Nat}
    {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {outcome : Control result}
    {body : Complexity.Language.Exec program stmt entry finish outcome}
    (safe : ScopeSafe entry.heap finish outcome)
    (bodyCore : ArenaCoreSimulates body w heapLimit depth cursor bodyCursor steps) :
    ArenaCoreSimulates (.scope body safe) w heapLimit depth cursor cursor (steps + 6) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  have positive : 0 < heapLimit := lt_of_lt_of_le arena.cursor_pos arena.cursor_le
  have avoidsMark : layout.Avoids next := fun v i => Nat.ne_of_lt (bounded v i)
  have boundedBody : layout.Bounded (next + 1) :=
    fun v i => Nat.lt_trans (bounded v i) (Nat.lt_succ_self next)
  have capturedMatches : layout.Matches placement entry.locals
      (s.setReg next (s.mem 0)).regs := matched.setReg_of_ne avoidsMark (s.mem 0)
  have capturedFlag : (s.setReg next (s.mem 0)).regs flag = 0 :=
    (Source.State.setReg_ne s next flag (s.mem 0) (Nat.ne_of_lt fresh)).trans flagZero
  have captured := Source.Arena.Scope.capture_measured
    (control := controlReg) (program := lowerProgram program) (depth := depth) next s positive
  obtain ⟨finalPlacement, middle, executed, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw placement layout (next + 1) resultSlot flag
      (s.setReg next (s.mem 0)) regular boundedBody capturedMatches avoids
      (Nat.lt_trans fresh (Nat.lt_succ_self next)) resultFlag copySafe
      rooted (arena.setReg next (s.mem 0)) capturedFlag
  have outsideResult : next ∉ valueRegs result resultSlot :=
    flag_not_mem_valueRegs result resultSlot next
      (Nat.le_trans resultFlag (Nat.le_of_lt fresh))
  have saved : middle.regs next = BitVec.ofNat w cursor := by
    calc
      middle.regs next = (s.setReg next (s.mem 0)).regs next :=
        lowerStmtCore_regs_eq executed.erase regular boundedBody avoidsMark
          (Nat.lt_succ_self next) outsideResult (Nat.ne_of_gt fresh)
      _ = s.mem 0 := Source.State.setReg_same s next (s.mem 0)
      _ = BitVec.ofNat w cursor := arena.cursor_eq
  have released : Source.LocalMeasuredExec controlReg (lowerProgram program) heapLimit depth
      (Source.Arena.Scope.release next) 3 middle
      (middle.setMem 0 (BitVec.ofNat w cursor)) := by
    simpa only [saved] using
      Source.Arena.Scope.release_measured (control := controlReg)
        (program := lowerProgram program) (depth := depth) next middle positive
  refine ⟨finalPlacement, middle.setMem 0 (BitVec.ofNat w cursor), ?_, ?_,
    arena.take finalArena body.heap_shapeExtends agreed, agreed, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Source.LocalMeasuredExec.seq captured (Source.LocalMeasuredExec.seq executed released)
  · cases outcome with
    | normal => exact property
    | returned value =>
      simpa only [ControlMatches, resultExprs, List.map_map, Source.State.eval, Expr.eval,
        Source.State.setMem] using property
    | fault error => exact property
  · intro separate
    exact finalMatches separate

end Ram.LanguageCompiler.ArenaCoreSimulates
