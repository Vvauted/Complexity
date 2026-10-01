/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured

/-!
# Measured buffer reads, writes and borrowed slices

Successful source operations retain their actual values or descriptors in the
continuation. The existing readiness and cost constructors supply finite-word
conditions and compiler counts. None of these operations allocates; any later cursor
growth belongs to the actual continuation.
-/

namespace Ram.LanguageCompiler.ArenaMeasured

open Complexity.Language

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {Γ : List Ty} {result : Ty}
variable {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
variable {entry : Complexity.Language.State Γ} {cursor : Nat}

/-- Read a proved source cell, then continue with its actual value and word range. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    {value : CellValue kind}
    (loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value)
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : index.eval entry.locals < 2 ^ w)
    (valueFits : ValueFits w (kind.toValue value))
    (body : ArenaMeasured program w heapLimit depth continuation
      (fun finish control finalCursor steps =>
        post finish.tail control finalCursor (readCodeSize + steps))
      (Complexity.Language.State.cons (kind.toValue value) entry) cursor) :
    ArenaMeasured program w heapLimit depth (.read buffer index continuation) post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish.tail, control, finalCursor, _, Complexity.Language.Exec.read loaded execution,
    ArenaReady.read (loaded := loaded) bufferFits indexFits valueFits ready,
    ArenaExecutionCost.read (loaded := loaded) (bufferFits := bufferFits)
      (indexFits := indexFits) (valueFits := valueFits) cost, outcome⟩

/-- Write the proved source cell and retain the actual updated heap. The cursor
is unchanged; aliasing and frames are properties of this same write equation. -/
theorem write {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {value : Atom Γ kind.toTy} {heap : Heap}
    (written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
      (kind.ofValue (value.eval entry.locals)) = .ok heap)
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (indexFits : index.eval entry.locals < 2 ^ w)
    (valueFits : ValueFits w (value.eval entry.locals))
    (outcome : post ⟨entry.locals, heap⟩ .normal cursor writeCodeSize) :
    ArenaMeasured program w heapLimit depth (.write buffer index value) post entry cursor := by
  exact ⟨⟨entry.locals, heap⟩, .normal, cursor, writeCodeSize,
    Complexity.Language.Exec.write written,
    ArenaReady.write (written := written) bufferFits indexFits valueFits,
    ArenaExecutionCost.write (written := written) (bufferFits := bufferFits)
      (indexFits := indexFits) (valueFits := valueFits), outcome⟩

/-- Borrow the actual successful slice without copying its cells or changing the
arena cursor. Placement conditions remain separate from descriptor word ranges. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {view : Buffer kind}
    (sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view)
    (bufferFits : ValueFits w (buffer.eval entry.locals))
    (offsetFits : offset.eval entry.locals < 2 ^ w)
    (lengthFits : length.eval entry.locals < 2 ^ w)
    (viewFits : ValueFits w (τ := .buffer kind) view)
    (body : ArenaMeasured program w heapLimit depth continuation
      (fun finish control finalCursor steps =>
        post finish.tail control finalCursor (sliceCodeSize + steps))
      (Complexity.Language.State.cons view entry) cursor) :
    ArenaMeasured program w heapLimit depth (.slice buffer offset length continuation)
      post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish.tail, control, finalCursor, _, Complexity.Language.Exec.slice sliced execution,
    ArenaReady.slice (sliced := sliced) bufferFits offsetFits lengthFits viewFits ready,
    ArenaExecutionCost.slice (sliced := sliced) (bufferFits := bufferFits)
      (offsetFits := offsetFits) (lengthFits := lengthFits) (viewFits := viewFits) cost, outcome⟩

end Ram.LanguageCompiler.ArenaMeasured
