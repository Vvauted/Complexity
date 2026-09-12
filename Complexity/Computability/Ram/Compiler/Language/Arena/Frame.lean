/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Basic
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic

/-!
# Arena initialization and ordinary writes across function boundaries

The session bootstrap is an actual structured source store. Its three machine
instructions come from the existing local compiler: two constant loads and a
store. Bootstrap establishes the metadata around already represented objects;
it is not a loader for those objects and must not be repeated between calls.

Successful typed writes retain the arena's cursor and reserved object extents.
Function return transports the callee's actual final arena through the existing
caller-register restoration, rather than restoring an old caller cursor.
These rules add no allocation, reclamation, execution relation or cost model.
-/

namespace Ram.Source.Arena

/-- Initialize the shared cursor once at the surrounding session boundary. -/
def bootstrap (next : Nat) : Stmt := .store (.const 0) (.const next)

/-- The bootstrap's count is the size of its actual generated instruction block. -/
theorem bootstrap_stmtSize (control : Nat) (localsTable : Nat → Nat) (next : Nat) :
    LocalCompiler.stmtSize control localsTable (bootstrap next) = 3 := rfl

/-- The two constant expressions and one store execute with their compiler count.
The stored word is modular; a surrounding arena representation supplies exactness. -/
theorem bootstrap_measured {control heapLimit depth : Nat} {program : Program}
    (entry : State w) (next : Nat) (positive : 0 < heapLimit) :
    LocalMeasuredExec control program heapLimit depth (bootstrap next) 3 entry
      (entry.setMem 0 (BitVec.ofNat w next)) := by
  simpa only [bootstrap, State.eval, Expr.eval] using
    (LocalMeasuredExec.store (control := control) (program := program)
      (d := depth) (s := entry) (address := .const 0) (value := .const next)
      trivial trivial (by simpa only [State.eval, Expr.eval, BitVec.toNat_ofNat,
        Nat.zero_mod] using positive))

end Ram.Source.Arena

namespace Ram.LanguageCompiler

open Complexity.Language

namespace ArenaRep

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Complexity.Language.Heap} {entry finish : Source.State w}

/-- Change local registers or streams without changing the represented shared memory. -/
theorem of_mem_eq (arena : ArenaRep placement next heapLimit heap entry)
    (same : finish.mem = entry.mem) : ArenaRep placement next heapLimit heap finish := by
  apply arena.of_mem_eq_on (Nat.le_refl _) arena.cursor_le
  · exact (congrFun same 0).trans arena.cursor_eq
  · intro address _ _
    exact congrFun same address

/-- Local assignments retain the complete shared arena. -/
theorem setReg (arena : ArenaRep placement next heapLimit heap entry) (r : Reg) (value : Word w) :
    ArenaRep placement next heapLimit heap (entry.setReg r value) := arena.of_mem_eq rfl

/-- Receiving fields changes registers, not the callee's actual shared arena. -/
theorem setRegs (arena : ArenaRep placement next heapLimit heap entry)
    (dsts : List Reg) (values : List (Word w)) :
    ArenaRep placement next heapLimit heap (entry.setRegs dsts values) :=
  arena.of_mem_eq (Source.State.setRegs_mem entry dsts values)

/-- A callee starts with the same shared objects and allocation cursor. -/
theorem enter (arena : ArenaRep placement next heapLimit heap entry) (args : List (Word w)) :
    ArenaRep placement next heapLimit heap (entry.enter args) := arena.of_mem_eq rfl

/-- Caller restoration retains the arena established by the callee. -/
theorem restore (arena : ArenaRep placement next heapLimit heap finish) (caller : Source.State w) :
    ArenaRep placement next heapLimit heap (caller.restore finish) := arena.of_mem_eq rfl

/-- A successful scalar-array write preserves shared metadata and all reserved
object extents. Overlapping views retain the existing heap-write semantics. -/
theorem write (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    {updated : Complexity.Language.Heap}
    (written : heap.write buffer index value = .ok updated)
    (valueFits : cellToNat value < 2 ^ w) :
    ArenaRep placement next heapLimit updated
      (entry.setMem (arrayAddr (bufferRef placement buffer).base index) (cellWord w value)) := by
  have represented := arena.heapRep.write written valueFits
  obtain ⟨values, found, extent, bound, rfl⟩ :=
    Complexity.Language.Heap.write_eq_ok_iff.mp written
  have absoluteBound : buffer.offset + index < values.size := by omega
  have addressNonzero : arrayAddr (bufferRef placement buffer).base index ≠ 0 := by
    simpa only [bufferRef, arrayAddr_add] using arena.address_ne_zero found absoluteBound
  refine ⟨represented, arena.cursor_pos, arena.cursor_le, arena.limit_lt, ?_, ?_⟩
  · exact (Source.State.setMem_ne entry _ 0 _ (Ne.symm addressNonzero)).trans arena.cursor_eq
  · intro other stored otherFound cell cellBound
    by_cases sameObject : buffer.object = other
    · subst other
      have updatedFound :
          (heap.replace buffer.object
            (values.setIfInBounds (buffer.offset + index) value)).objects[buffer.object]? =
            some (.buffer τ (values.setIfInBounds (buffer.offset + index) value)) :=
        Complexity.Language.Heap.object?_eq_some_iff.mp
          (Complexity.Language.Heap.object?_replace_self
            (Complexity.Language.Heap.object_lt_size found))
      have sameStored : stored =
          .buffer τ (values.setIfInBounds (buffer.offset + index) value) :=
        Option.some.inj (otherFound.symm.trans updatedFound)
      subst stored
      exact arena.reserved found cell (by
        simpa only [heapObjectWords_buffer_size, Array.size_setIfInBounds] using cellBound)
    · have oldFound : heap.objects[other]? = some stored := by
        simpa only [Complexity.Language.Heap.replace,
          Array.getElem?_setIfInBounds_ne sameObject] using otherFound
      exact arena.storedReserved oldFound cell cellBound

/-- Bootstrap establishes an arena around supplied objects using a real counted
store. Their initial representation and positive reserved placement remain inputs;
this theorem does not assign a zero cost to loading their contents. -/
theorem bootstrap {control depth : Nat} {program : Program}
    (represented : HeapRep placement heapLimit heap entry)
    (positive : 0 < next) (capacity : next ≤ heapLimit) (fits : heapLimit < 2 ^ w)
    (reserved : ∀ {object : Nat} {stored : HeapObject},
      heap.objects[object]? = some stored →
        ∀ index, index < (heapObjectWords placement stored).size →
          0 < (arrayAddr (placement object) index).toNat ∧
            (arrayAddr (placement object) index).toNat < next) :
    Source.LocalMeasuredExec control program heapLimit depth (Source.Arena.bootstrap next)
        3 entry (entry.setMem 0 (BitVec.ofNat w next)) ∧
      ArenaRep placement next heapLimit heap (entry.setMem 0 (BitVec.ofNat w next)) := by
  refine ⟨Source.Arena.bootstrap_measured entry next (lt_of_lt_of_le positive capacity),
    ?_, positive, capacity, fits, Source.State.setMem_same _ _ _, reserved⟩
  apply represented.of_mem_eq_on
  intro object stored found index bound
  apply Source.State.setMem_ne
  intro same
  have cellPositive := (reserved found index bound).1
  simp [same] at cellPositive

/-- A completed invocation retains its actual callee arena, including cursor
updates, while restoring caller registers. The heap and cursor in the body
postcondition may differ from those at entry. -/
theorem of_functionExec {program : Program} {depth : Nat} {f : Func}
    {args values : List (Word w)}
    (execution : Source.FunctionExec program heapLimit depth f args entry values finish)
    (body : ∀ callee, Source.SafeExec program heapLimit depth f.body (entry.enter args) callee →
      ArenaRep placement next heapLimit heap callee) :
    ArenaRep placement next heapLimit heap finish := by
  obtain ⟨_, _, callee, executed, _, _, rfl⟩ := execution
  exact (body callee executed).of_mem_eq (Source.State.restore_mem entry callee)

end ArenaRep

end Ram.LanguageCompiler
