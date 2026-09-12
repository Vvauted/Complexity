/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Heap.Node
import Complexity.Computability.Ram.Compiler.Language.Heap

/-!
# Reading represented immutable nodes

The existing complete-object representation stores a node in three real words:
its scalar head, an optional-tail tag and the tail's actual placed address.
These projections expose those same words and their bounds. They do not identify
source object numbers with machine addresses or reinterpret arbitrary words as
typed references.

An ordinary list observation connects typed `Heap.uncons` to this storage and
retains the same shared tail. Nil reads no node. These are representation facts,
not a new evaluator, a machine execution or an assigned instruction count.
-/

namespace Ram.LanguageCompiler.HeapRep

open Complexity.Language

variable {w heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Heap} {target : Source.State w}

/-- All three fields read back the head, option tag and actual tail address.
The tag distinguishes nil independently of the numeric address of a live tail. -/
theorem node_fields (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) :
    target.mem (placement object) = cellWord w head ∧
      target.mem (arrayAddr (placement object) 1) = (if tail.isSome then 1 else 0) ∧
      target.mem (arrayAddr (placement object) 2) =
        tail.elim 0 (fun ref => placement ref.object) := by
  have stored := represented.nodes found
  have length : (heapObjectWords placement (.node τ head tail)).toList.length = 3 := by
    simp only [Array.length_toList, heapObjectWords_node_size]
  have first := stored.1.lookup 0 (by omega)
  have second := stored.1.lookup 1 (by omega)
  have third := stored.1.lookup 2 (by omega)
  cases tail <;>
    simpa [heapObjectWords, arrayAddr] using And.intro first (And.intro second third)

/-- The scalar payload has its exact mathematical value, not a residue modulo
the word size. Boolean heads use the same existing zero-or-one observation. -/
theorem node_head_toNat (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) :
    (target.mem (placement object)).toNat = cellToNat head := by
  rw [(represented.node_fields found).1]
  exact cellWord_toNat (represented.fit (Heap.node?_eq_some_iff.mp found)).1

/-- Each of the three loads lies below the heap boundary and has its exact
non-wrapping offset. The interval includes the optional tail's storage word. -/
theorem node_address (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {object : Nat} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (found : heap.node? τ object = some (head, tail)) {index : Nat} (bound : index < 3) :
    (arrayAddr (placement object) index).toNat = (placement object).toNat + index ∧
      (arrayAddr (placement object) index).toNat < heapLimit := by
  have stored := represented.nodes found
  have encodedBound : index <
      (heapObjectWords placement (.node τ head tail)).toList.length := by
    simpa only [Array.length_toList, heapObjectWords_node_size] using bound
  exact ⟨stored.1.addr_toNat encodedBound, stored.addr_lt encodedBound⟩

/-- The represented node invariant is precisely the source heap's concrete
backward-link condition. Buffer payloads are not treated as references. -/
theorem node_backward (represented : HeapRep placement heapLimit heap target) :
    Heap.BackwardLinks Heap.nodeReferences heap := by
  rintro source destination ⟨object, found, member⟩
  cases object with
  | buffer τ values => simp [Heap.nodeReferences] at member
  | node τ head tail =>
      cases tail with
      | none => simp [Heap.nodeReferences] at member
      | some tail =>
          have same : destination = tail.object := by
            simpa only [Heap.nodeReferences, List.mem_singleton] using member
          subst destination
          exact represented.backward (Heap.node?_eq_some_iff.mpr found)

/-- Typed uncons of an observed list returns the same head and shared tail
whose three-word node is represented in RAM. Nil requires no node load. -/
theorem uncons_contents (represented : HeapRep placement heapLimit heap target)
    {τ : CellTy} {root : Option (NodeRef τ)} {values : List (CellValue τ)}
    (observed : NodeRef.Contents heap root values) :
    match values with
    | [] => root = none ∧ heap.uncons root = .ok none
    | head :: rest => ∃ ref tail,
        root = some ref ∧
        heap.uncons root = .ok (some (head, tail)) ∧
        NodeRef.Contents heap tail rest ∧
        Source.ArrayAt heapLimit (placement ref.object)
          (heapObjectWords placement (.node τ head tail)).toList target := by
  cases observed with
  | nil => exact ⟨rfl, rfl⟩
  | cons found tail =>
      exact ⟨_, _, rfl, Heap.uncons_some_eq found, tail, represented.nodes found⟩

end Ram.LanguageCompiler.HeapRep
