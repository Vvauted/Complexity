/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Execution.Memory
import Ram.Memory
import Ram.Array

/-!
# Memory frames at every real execution prefix

Cumulative footprints are monotone in their transition horizon. Therefore an
address outside the whole write set is unchanged at every real prefix, not
merely restored to its original value at the endpoint. The whole requested
horizon need not exist; the prefix being observed must have an actual `Exec`.

These results use the existing write set, heap agreement and array assertions.
They do not infer absence of intermediate writes from final memory equality,
and they do not identify distinct visited addresses with live allocation.
-/

namespace Ram

/-- Extending the observation horizon cannot remove an actual heap access. -/
theorem heapAccesses_mono (code : Code) (start : State w) {n m : Nat} (hle : n ≤ m) :
    heapAccesses code n start ⊆ heapAccesses code m start := by
  intro address member
  obtain ⟨k, hk, current, next, execution, transition, access⟩ :=
    mem_heapAccesses_iff.mp member
  exact mem_heapAccesses_iff.mpr
    ⟨k, hk.trans_le hle, current, next, execution, transition, access⟩

/-- Extending the observation horizon cannot remove an actual heap write. -/
theorem heapWrites_mono (code : Code) (start : State w) {n m : Nat} (hle : n ≤ m) :
    heapWrites code n start ⊆ heapWrites code m start := by
  intro address member
  obtain ⟨k, hk, current, next, execution, transition, write⟩ :=
    mem_heapWrites_iff.mp member
  exact mem_heapWrites_iff.mpr
    ⟨k, hk.trans_le hle, current, next, execution, transition, write⟩

namespace Exec

variable {code : Code} {n k : Nat} {start current : State w}

/-- A word outside the entire write set is unchanged at every actual prefix,
including the initial and final states when they are in the given horizon. -/
theorem prefix_mem_eq_of_not_written (execution : Exec code k start current)
    (hk : k ≤ n) {address : Word w} (unwritten : address ∉ heapWrites code n start) :
    current.mem address = start.mem address :=
  execution.mem_eq_of_not_written
    (fun member => unwritten (heapWrites_mono code start hk member))

/-- A genuinely empty write set preserves the entire heap throughout every
actual prefix. This is stronger than equality only at the final state. -/
theorem prefix_mem_eq_of_heapWrites_empty (execution : Exec code k start current)
    (hk : k ≤ n) (writes : heapWrites code n start = ∅) : current.mem = start.mem := by
  funext address
  exact execution.prefix_mem_eq_of_not_written hk (by simp [writes])

/-- If all writes are in the private region above a boundary, every actual
prefix preserves the complete source-visible heap below that boundary. -/
theorem prefix_heapEqBelow_of_writes_above (execution : Exec code k start current)
    (hk : k ≤ n) (limit : Nat)
    (above : ∀ address ∈ heapWrites code n start, limit ≤ address.toNat) :
    HeapEqBelow limit start.mem current.mem := by
  intro address hlt
  apply (execution.prefix_mem_eq_of_not_written hk ?_).symm
  intro member
  exact (Nat.not_le_of_lt hlt) (above address member)

/-- An already represented array survives at every real prefix if none of its
element addresses is written. The original fit condition and contents are
retained; this neither allocates an array nor presumes the rest of memory is
unchanged. -/
theorem prefix_arrayRep_of_not_written (execution : Exec code k start current)
    (hk : k ≤ n) {base : Word w} {xs : List (Word w)}
    (array : ArrayRep start.mem base xs)
    (unwritten : ∀ i, i < xs.length → arrayAddr base i ∉ heapWrites code n start) :
    ArrayRep current.mem base xs := by
  refine ⟨array.fits, ?_⟩
  intro i hi
  rw [execution.prefix_mem_eq_of_not_written hk (unwritten i hi)]
  exact array.lookup i hi

end Exec
end Ram
