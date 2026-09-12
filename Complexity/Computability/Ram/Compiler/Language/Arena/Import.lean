/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Frame
import Complexity.Language.Heap.Shape
import Complexity.Computability.Ram.Compiler.Language.Heap.Shape

/-!
# Importing heap-mutating functions into an arena session

A legacy function may change represented object contents without changing the
session's allocation metadata. Its actual final heap representation, an explicit
frame at address zero and containment of final object shapes suffice to recover
the arena representation. Safe execution alone supplies no metadata frame.

The shape premise runs from the final heap to the initial heap: every final
object must already have had that type and extent in the reserved region. It
does not assert preservation of old contents or retention of every initial
object. Retaining caller roots additionally needs the source contract's forward
shape or rootedness guarantee. An allocating import instead supplies a complete
final arena, with its actual placement and advanced cursor.

These rules reuse the existing function execution and caller restoration.
Measured invocations use their existing `erase` theorem without changing their
count; function contracts transfer their postconditions through their existing
`post` theorem. No new execution or import-contract relation is introduced.
-/

namespace Ram.LanguageCompiler.ArenaRep

open Complexity.Language

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {initialHeap finalHeap : Complexity.Language.Heap} {entry finish : Source.State w}

/-- Rebuild the arena after a legacy function changes object contents. Only
metadata is framed; the supplied final representation describes the actual
mutated heap. The reverse shape premise excludes fresh final object slots. -/
theorem of_heapRep (arena : ArenaRep placement next heapLimit initialHeap entry)
    (represented : HeapRep placement heapLimit finalHeap finish)
    (shape : finalHeap.ShapeExtends initialHeap)
    (metadata : finish.mem 0 = entry.mem 0) :
    ArenaRep placement next heapLimit finalHeap finish := by
  refine ⟨represented, arena.cursor_pos, arena.cursor_le, arena.limit_lt,
    metadata.trans arena.cursor_eq, ?_⟩
  intro object stored found index bound
  obtain ⟨previous, oldFound, sameSize⟩ :=
    heapObjectWords_size_of_shapeExtends shape placement found
  exact arena.storedReserved oldFound index (by simpa only [sameSize] using bound)

/-- Import a nonallocating body's final heap and metadata frame through the
actual invocation. Caller-local restoration retains the callee's changed
objects; no unchanged-heap or whole-memory premise is needed. -/
theorem of_functionExec_frame {program : Ram.Program} {depth : Nat} {f : Func}
    {args values : List (Word w)}
    (arena : ArenaRep placement next heapLimit initialHeap entry)
    (execution : Source.FunctionExec program heapLimit depth f args entry values finish)
    (shape : finalHeap.ShapeExtends initialHeap)
    (body : ∀ callee, Source.SafeExec program heapLimit depth f.body (entry.enter args) callee →
      HeapRep placement heapLimit finalHeap callee ∧ callee.mem 0 = entry.mem 0) :
    ArenaRep placement next heapLimit finalHeap finish := by
  apply of_functionExec execution
  intro callee executed
  obtain ⟨represented, metadata⟩ := body callee executed
  exact arena.of_heapRep represented shape metadata

end Ram.LanguageCompiler.ArenaRep
