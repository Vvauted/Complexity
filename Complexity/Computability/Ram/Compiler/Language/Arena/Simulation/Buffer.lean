/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Basic
import Complexity.Computability.Ram.Compiler.Language.MeasuredValues

/-!
# Buffer bindings around allocating continuations

Reads and slices use the existing measured lowering and keep the actual shared
heap and arena cursor. Their scoped continuations may allocate and return a new
placement. Each rule retains that final placement, heap and control outcome,
dropping only the added lexical binding from the local correspondence.

Scalar reads introduce no object roots. Slice roots follow their existing
object identifier, without strengthening source validity or aliasing premises.
The counts cover actual load or descriptor work plus the supplied continuation.
-/

namespace Ram.LanguageCompiler.ArenaCoreSimulates

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {Γ : List Ty} {result : Ty} {w heapLimit depth cursor finalCursor steps : Nat}

/-- Bind a real shared-heap read before an allocation-aware continuation. The
scalar receiver changes registers only; the continuation retains its actual
final arena and the agreement protecting all original object placements. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {finish : Complexity.Language.State (kind.toTy :: Γ)} {outcome : Control result}
    {value : CellValue kind}
    {loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons (kind.toValue value) entry) finish outcome}
    (bodyCore : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps)
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : index.eval entry.locals < 2 ^ w)
    (valueFits : ValueFits w (kind.toValue value)) :
    ArenaCoreSimulates (.read loaded body) w heapLimit depth cursor finalCursor
      (readCodeSize + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨first, _, _⟩ := lowerRead_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout next buffer index entry.locals s hw matched arena.heapRep bufferFits indexFits loaded
  rw [lowerRead_stmtSize] at first
  have matching : RegisterMap.Matches (RegisterMap.extend layout kind.toTy next) placement
      (Env.cons (kind.toValue value) entry.locals)
      (s.setRegs (valueRegs kind.toTy next)
        (valueWords placement (kind.toValue value))).regs :=
    matched.setRegs (τ := kind.toTy) bounded (kind.toValue value) valueFits
  have flagPreserved := (valueRegs_setRegs_other s kind.toTy next flag
    (valueWords placement (kind.toValue value))
    (flag_not_mem_valueRegs_of_lt kind.toTy next flag fresh)).trans flagZero
  have continuationRooted :
      (Complexity.Language.State.cons (kind.toValue value) entry).locals.Rooted entry.heap :=
    rooted.cons _ (CellTy.toValue_rooted entry.heap kind value)
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw placement (RegisterMap.extend layout kind.toTy next)
      (next + fieldCount kind.toTy) resultSlot flag _
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

/-- Bind the actual checked slice descriptor before an allocating continuation.
The descriptor keeps the borrowed object's root and aliases; heap and cursor
are unchanged until the continuation runs at that same represented state. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {finish : Complexity.Language.State (.buffer kind :: Γ)} {outcome : Control result}
    {view : Buffer kind}
    {sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view}
    {body : Complexity.Language.Exec program continuation
      (Complexity.Language.State.cons view entry) finish outcome}
    (bodyCore : ArenaCoreSimulates body w heapLimit depth cursor finalCursor steps)
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (offsetFits : offset.eval entry.locals < 2 ^ w)
    (lengthFits : length.eval entry.locals < 2 ^ w)
    (viewFits : ValueFits w (τ := .buffer kind) view) :
    ArenaCoreSimulates (.slice sliced body) w heapLimit depth cursor finalCursor
      (sliceCodeSize + steps) := by
  intro controlReg hw placement layout next resultSlot flag s regular bounded matched avoids
    fresh resultFlag copySafe rooted arena flagZero
  obtain ⟨first, _, _⟩ := lowerSlice_measured (control := controlReg)
    (program := lowerProgram program) (heapLimit := heapLimit) (depth := depth)
    layout next buffer offset length entry.locals s hw matched arena.heapRep
    bufferFits offsetFits lengthFits bounded sliced
  rw [lowerSlice_stmtSize] at first
  have matching : RegisterMap.Matches (RegisterMap.extend layout (.buffer kind) next) placement
      (Env.cons (τ := .buffer kind) view entry.locals)
      (s.setRegs (valueRegs (.buffer kind) next)
        (valueWords placement (τ := .buffer kind) view)).regs :=
    matched.setRegs (τ := .buffer kind) bounded view viewFits
  have flagPreserved := (valueRegs_setRegs_other s (.buffer kind) next flag
    (valueWords placement (τ := .buffer kind) view)
    (flag_not_mem_valueRegs_of_lt (.buffer kind) next flag fresh)).trans flagZero
  have bufferRooted : (buffer.eval entry.locals).Rooted entry.heap := buffer.eval_rooted rooted
  have viewRooted : view.Rooted entry.heap := Buffer.Rooted.slice bufferRooted sliced
  have continuationRooted :
      (Complexity.Language.State.cons (τ := .buffer kind) view entry).locals.Rooted entry.heap :=
    Env.Rooted.cons (τ := .buffer kind) rooted view viewRooted
  obtain ⟨finalPlacement, t, rest, property, finalArena, agreed, finalMatches⟩ :=
    bodyCore controlReg hw placement (RegisterMap.extend layout (.buffer kind) next)
      (next + fieldCount (.buffer kind)) resultSlot flag _
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
