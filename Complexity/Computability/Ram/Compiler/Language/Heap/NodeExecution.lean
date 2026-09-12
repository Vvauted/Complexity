/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap.Node
import Complexity.Computability.Ram.Memory.Node

/-!
# Actual reads of represented immutable nodes

The shared three-load block reads the head, option tag and placed tail address
of the same source node. Its exact compiler-derived execution preserves the
complete represented heap, including other nodes and scalar arrays. Register
and stream frames come from that block's actual endpoint.

The linked-list rule starts from ordinary `NodeRef.Contents` and returns the
actual stored tail with its mathematical contents. It neither reconstructs a
source identifier from an address nor copies the suffix. This module handles a
nonempty root; an outer option branch, source-statement integration and frontend
uncons syntax are separate operations.
-/

namespace Ram.LanguageCompiler.HeapRep

open Complexity.Language

variable {w heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Heap} {entry : Source.State w}

/-- Read all three fields of the actual typed node with the existing measured
execution. The final head is exact, and the same complete heap remains represented.
The base register may be the final tail destination. -/
theorem node_read (represented : HeapRep placement heapLimit heap entry)
    (r : Source.Node.Registers) {program : Program} {control depth : Nat}
    {τ : CellTy} {ref : NodeRef τ} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ ref.object = some (head, tail))
    (base_reg : entry.regs r.base = placement ref.object) :
    Source.LocalMeasuredExec control program heapLimit depth r.read
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) r.read)
        entry (r.loaded entry) ∧
      r.Post heapLimit (placement ref.object) (cellWord w head)
        (if tail.isSome then 1 else 0) (tail.elim 0 (fun next => placement next.object))
        entry (r.loaded entry) ∧
      HeapRep placement heapLimit heap (r.loaded entry) ∧
      ((r.loaded entry).regs r.head).toNat = cellToNat head := by
  have array : Source.ArrayAt heapLimit (placement ref.object)
      [cellWord w head, if tail.isSome then 1 else 0,
        tail.elim 0 (fun next => placement next.object)] entry := by
    cases tail <;> simpa [heapObjectWords] using represented.nodes found
  have pre : r.Pre heapLimit (placement ref.object) (cellWord w head)
      (if tail.isSome then 1 else 0) (tail.elim 0 (fun next => placement next.object)) entry :=
    ⟨array, base_reg⟩
  obtain ⟨execution, post⟩ := r.read_measured (program := program) (control := control)
    (depth := depth) pre
  have retained : HeapRep placement heapLimit heap (r.loaded entry) := by
    unfold Source.Node.Registers.loaded
    exact ((represented.setReg _ _).setReg _ _).setReg _ _
  refine ⟨execution, post, retained, ?_⟩
  rw [post.head_reg]
  exact cellWord_toNat (represented.fit (Heap.node?_eq_some_iff.mp found)).1

/-- The actual nonempty-list read returns its mathematical head and unchanged
shared tail. The tail observation and all original heap objects remain available
at the endpoint of the same counted execution; no disjointness of list roots is needed. -/
theorem list_cons_read (represented : HeapRep placement heapLimit heap entry)
    (r : Source.Node.Registers) {program : Program} {control depth : Nat}
    {τ : CellTy} {ref : NodeRef τ} {head : CellValue τ} {rest : List (CellValue τ)}
    (observed : NodeRef.Contents heap (some ref) (head :: rest))
    (base_reg : entry.regs r.base = placement ref.object) :
    ∃ tail : Option (NodeRef τ),
      heap.uncons (some ref) = .ok (some (head, tail)) ∧
      NodeRef.Contents heap tail rest ∧
      Source.LocalMeasuredExec control program heapLimit depth r.read
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) r.read)
        entry (r.loaded entry) ∧
      r.Post heapLimit (placement ref.object) (cellWord w head)
        (if tail.isSome then 1 else 0) (tail.elim 0 (fun next => placement next.object))
        entry (r.loaded entry) ∧
      HeapRep placement heapLimit heap (r.loaded entry) ∧
      ((r.loaded entry).regs r.head).toNat = cellToNat head := by
  cases observed with
  | cons found contents =>
      exact ⟨_, Heap.uncons_some_eq found, contents,
        represented.node_read r (program := program) (control := control)
          (depth := depth) found base_reg⟩

end Ram.LanguageCompiler.HeapRep
