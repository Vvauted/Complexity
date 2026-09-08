/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Search.Total
import Complexity.Computability.Ram.Verification.Time.Composition

/-!
# Separate logarithmic time bound for lower-bound search

The same budget-free iteration specification supplies interval halving to the
generic division-loop rule. The body bound charges its generated instructions;
the loop rule adds each actual guard, backedge and final failed guard.
-/

namespace Ram.Source.Array.Search

/-- Every completed search loop has logarithmic execution time. Functional
correctness and termination are supplied independently by `loop_total`. -/
theorem loop_timeBound (registers : Registers) {control heapLimit depth : Nat}
    {program : Program} {base key : Word w} {xs : List (Word w)} (hw : 2 ≤ w)
    (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) (original : State w) :
    TimeBound control program heapLimit depth (loop registers)
      (Invariant registers heapLimit base key xs original)
      (fun s => Nat.clog 2 ((s.regs registers.hi).toNat -
        (s.regs registers.lo).toNat + 1) * 25 + 4) := by
  apply TimeBound.while_div 2 (by decide)
    (Invariant registers heapLimit base key xs original)
    (fun s => (s.regs registers.hi).toNat - (s.regs registers.lo).toNat) 20
  · intro s invariant nonzero
    have order := condition_positive registers invariant nonzero
    omega
  · exact iteration_total registers hw sorted
  · rintro s ⟨invariant, nonzero⟩
    obtain ⟨within, _⟩ := search_address registers hw invariant nonzero
    exact (body_contract registers (by omega) s within).timeBound s rfl

end Ram.Source.Array.Search
