/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap.Node
import Complexity.Computability.Ram.Compiler.Language.Placement
import Complexity.Computability.Ram.Compiler.Language.Arena.Basic

/-!
# Representing a completed immutable-node allocation

An initialized fresh three-word interval represents the single node appended
by `Heap.cons`. Its tail word contains the existing tail's actual placement;
only the new object's placement changes. All older objects, including nodes
with shared tails and mutable buffers, retain their complete representation.

An existing tail root establishes old-domain membership. The new node keeps
the concrete backward-link invariant without requiring a complete list proof.
The list specialization additionally preserves its typed contents. These rules
consume the runtime's initialization, cursor and frame facts; they do not
execute an allocator, traverse the tail or assign a constant instruction count.
-/

namespace Ram.LanguageCompiler.ArenaRep

open Complexity.Language

variable {w next heapLimit : Nat} {placement : Nat → Word w}
variable {heap : Heap} {entry finish : Source.State w}

/-- One completed initialization extends the arena by the actual three-word
node. The optional tail must name an old object, but need not represent a list.
Stored type and list contents remain independent semantic properties. -/
theorem cons_of_rooted (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {head : CellValue τ} {tail : Option (NodeRef τ)}
    (rooted : ValueRooted heap (τ := .option (.node τ)) tail)
    (headFits : cellToNat head < 2 ^ w)
    (capacity : next + 3 ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + 3))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (heapObjectWords placement (.node τ head tail)).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + 3) heapLimit (heap.cons head tail).2 finish := by
  have oldArena := arena.of_mem_eq_on (Nat.le_add_right next 3) capacity cursor same
  let placed := Function.update placement heap.objects.size (BitVec.ofNat w next)
  have agreed : Placement.Agrees heap placement placed :=
    Placement.agrees_update heap placement (Nat.le_refl heap.objects.size)
      (BitVec.ofNat w next)
  have oldRepresented := oldArena.heapRep.placement agreed
  have encoded : heapObjectWords placed (.node τ head tail) =
      heapObjectWords placement (.node τ head tail) := by
    cases tail with
    | none => rfl
    | some ref =>
        simp only [heapObjectWords, ← agreed rooted]
  have initialized' : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (heapObjectWords placed (.node τ head tail)).toList finish := by
    rw [encoded]
    exact initialized
  have retained : ∀ {object : Nat} {stored : HeapObject},
      heap.objects[object]? = some stored →
        ∀ index, index < (heapObjectWords placed stored).size →
          0 < (arrayAddr (placed object) index).toNat ∧
            (arrayAddr (placed object) index).toNat < next := by
    intro object stored found index bound
    rw [← agreed (Array.getElem?_eq_some_iff.mp found).choose]
    exact arena.storedReserved found index (by
      rw [heapObjectWords_size_eq placement placed stored]
      exact bound)
  have fresh : ∀ {stored : HeapObject},
      (heap.cons head tail).2.objects[heap.objects.size]? = some stored →
      Source.ArrayAt heapLimit (BitVec.ofNat w next)
        (heapObjectWords placed stored).toList finish ∧
      heapObjectFits w stored ∧
      (∀ index, index < (heapObjectWords placed stored).size →
        next ≤ (arrayAddr (BitVec.ofNat w next) index).toNat ∧
          (arrayAddr (BitVec.ofNat w next) index).toNat < next + 3) := by
    intro stored found
    have sameStored : stored = .node τ head tail :=
      Option.some.inj (found.symm.trans Array.getElem?_push_size)
    subst stored
    refine ⟨initialized', ⟨headFits, ?_⟩, ?_⟩
    · have limit := arena.limit_lt
      omega
    · intro index bound
      have indexBound : index < 3 := by
        simpa only [heapObjectWords_node_size] using bound
      have encodedBound : index <
          (heapObjectWords placed (.node τ head tail)).toList.length := by
        simpa only [Array.length_toList] using bound
      have address := initialized'.1.addr_toNat encodedBound
      rw [Word.ofNat_toNat_of_lt (lt_of_le_of_lt arena.cursor_le arena.limit_lt)] at address
      omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, lt_of_lt_of_le arena.cursor_pos (Nat.le_add_right next 3),
    capacity, arena.limit_lt, cursor, ?_⟩
  · intro object stored found
    by_cases isFresh : object = heap.objects.size
    · subst object
      simpa only [placed, Function.update_self] using (fresh found).1
    · exact oldRepresented.stored
        ((heap.getElem?_cons_of_ne head tail isFresh).symm.trans found)
  · intro object stored found
    by_cases isFresh : object = heap.objects.size
    · subst object
      exact (fresh found).2.1
    · exact oldRepresented.fit
        ((heap.getElem?_cons_of_ne head tail isFresh).symm.trans found)
  · intro object other stored otherStored found otherFound different
      index bound otherIndex otherBound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have oldFound := (heap.getElem?_cons_of_ne head tail different.symm).symm.trans otherFound
      have below := (retained oldFound otherIndex otherBound).2
      have above := (fresh found).2.2 index bound |>.1
      simp only [Function.update_self]
      intro equal
      change arrayAddr (BitVec.ofNat w next) index = arrayAddr (placed other) otherIndex at equal
      rw [equal] at above
      omega
    · by_cases otherFresh : other = heap.objects.size
      · subst other
        have oldFound := (heap.getElem?_cons_of_ne head tail isFresh).symm.trans found
        have below := (retained oldFound index bound).2
        have above := (fresh otherFound).2.2 otherIndex otherBound |>.1
        simp only [Function.update_self]
        intro equal
        change arrayAddr (placed object) index = arrayAddr (BitVec.ofNat w next) otherIndex at equal
        rw [← equal] at above
        omega
      · exact oldRepresented.disjoint
          ((heap.getElem?_cons_of_ne head tail isFresh).symm.trans found)
          ((heap.getElem?_cons_of_ne head tail otherFresh).symm.trans otherFound)
          different index bound otherIndex otherBound
  · intro kind object nodeHead nodeTail found
    have backward : Heap.BackwardLinks Heap.nodeReferences (heap.cons head tail).2 := by
      apply arena.heapRep.node_backward.push (.node τ head tail)
      intro target member
      cases tail with
      | none => simp [Heap.nodeReferences] at member
      | some ref =>
          have same : target = ref.object := by
            simpa only [Heap.nodeReferences, List.mem_singleton] using member
          exact same.symm ▸ (show ref.object < heap.objects.size from rooted)
    exact backward.node_tail_lt found
  · intro object stored found index bound
    by_cases isFresh : object = heap.objects.size
    · subst object
      have bounds := (fresh found).2.2 index bound
      simp only [Function.update_self]
      exact ⟨lt_of_lt_of_le arena.cursor_pos bounds.1, bounds.2⟩
    · have oldFound := (heap.getElem?_cons_of_ne head tail isFresh).symm.trans found
      have bounds := retained oldFound index bound
      exact ⟨bounds.1, lt_of_lt_of_le bounds.2 (Nat.le_add_right next 3)⟩

/-- One completed three-word initialization extends the arena by the actual
new node. Tail contents are a logical precondition, not a runtime traversal. -/
theorem cons (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {head : CellValue τ} {tail : Option (NodeRef τ)}
    {values : List (CellValue τ)}
    (observed : NodeRef.Contents heap tail values)
    (headFits : cellToNat head < 2 ^ w)
    (capacity : next + 3 ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + 3))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (heapObjectWords placement (.node τ head tail)).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + 3) heapLimit (heap.cons head tail).2 finish := by
  apply arena.cons_of_rooted (head := head) (tail := tail) ?_
    headFits capacity cursor initialized same
  cases tail with
  | none => trivial
  | some ref => exact observed.root_lt_size

/-- The same completed allocation represents the ordinary list constructor
while preserving every older list observation, including shared suffixes. -/
theorem cons_contents (arena : ArenaRep placement next heapLimit heap entry)
    {τ : CellTy} {head : CellValue τ} {tail : Option (NodeRef τ)}
    {values : List (CellValue τ)}
    (observed : NodeRef.Contents heap tail values)
    (headFits : cellToNat head < 2 ^ w)
    (capacity : next + 3 ≤ heapLimit)
    (cursor : finish.mem 0 = BitVec.ofNat w (next + 3))
    (initialized : Source.ArrayAt heapLimit (BitVec.ofNat w next)
      (heapObjectWords placement (.node τ head tail)).toList finish)
    (same : ∀ address : Word w, 0 < address.toNat → address.toNat < next →
      finish.mem address = entry.mem address) :
    ArenaRep (Function.update placement heap.objects.size (BitVec.ofNat w next))
      (next + 3) heapLimit (heap.cons head tail).2 finish ∧
      NodeRef.Contents (heap.cons head tail).2
        (some (heap.cons head tail).1) (head :: values) ∧
      (∀ {σ : CellTy} {root : Option (NodeRef σ)} {xs : List (CellValue σ)},
        NodeRef.Contents heap root xs → NodeRef.Contents (heap.cons head tail).2 root xs) :=
  ⟨arena.cons observed headFits capacity cursor initialized same,
    Heap.cons_contents head observed, fun old => old.node_alloc head tail⟩

end Ram.LanguageCompiler.ArenaRep
