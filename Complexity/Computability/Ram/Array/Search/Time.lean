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

/-- Every completed midpoint/update body uses at most twenty instructions.
The assignment costs eight, and the longer conditional branch costs twelve.
This conditional bound needs no address, correctness or word-width premise. -/
theorem body_timeBound (registers : Registers) {w control heapLimit depth : Nat}
    {program : Program} :
    TimeBound (w := w) control program heapLimit depth (body registers)
      (fun _ => True) (fun _ => 20) := by
  intro s _ steps t execution
  have atState : TimeBound control program heapLimit depth (body registers)
      (fun current => current = s) (fun _ => 20) := by
    apply TimeBound.assign_seq_at
    · change 8 ≤ 20
      decide
    · apply (TimeBound.ite (condition := comparison registers)
        (TimeBound.assign (dst := registers.lo)
          (value := .bin .add (.var registers.mid) (.const 1)))
        (TimeBound.assign (dst := registers.hi) (value := .var registers.mid))).mono_budget
      intro current _
      change 6 + 1 + (if current.eval (comparison registers) = 0 then 2 else 4 + 1) ≤ 20 - 8
      split <;> decide
  exact atState s rfl steps t execution

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
  · exact (body_timeBound registers).consequence
      (fun _ _ => trivial) (fun _ _ => Nat.le_refl _)

end Ram.Source.Array.Search
