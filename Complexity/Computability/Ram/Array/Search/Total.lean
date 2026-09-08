/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Search
import Complexity.Tactic.Ram.Total

/-!
# Budget-free total correctness of lower-bound search

The body follows the existing parameterized search step. The loop terminates
by strict descent of the natural interval length `hi - lo`; the stronger
halving property comes from the shared search invariant. No instruction count,
compiler register boundary or proposed time bound appears in these proofs.

The loop accepts the full search invariant, so a caller can initialize its own
named endpoints and retain the original shared state in the postcondition.
Array-read safety, representable midpoint arithmetic, sortedness and the actual
exit specification are the same as in the search core.
-/

namespace Ram.Source.Array.Search

/-- One safe search step, proved directly through budget-free statement rules.
The midpoint read must lie in the source heap; no time contract is erased here. -/
theorem body_total (registers : Registers) {heapLimit depth : Nat} {program : Program}
    (hw : 0 < w) (s : State w)
    (haddress : (s.regs registers.base + midpointWord registers s).toNat < heapLimit) :
    TotalContract program heapLimit depth (body registers) (fun t => t = s)
      (fun t => t = step registers s) := by
  intro t ht
  subst t
  change Verification.TotalWP program heapLimit depth (body registers)
    (fun finish => finish = step registers s) s
  ram_total_bind mid hmid [body]
  change mid = midpointWord registers s at hmid
  have addressSafe : (s.regs registers.base + mid).toNat < heapLimit := by
    simpa only [hmid] using haddress
  by_cases hcmp : (s.mem (s.regs registers.base + mid)).toNat <
      (s.regs registers.key).toNat
  all_goals
    ram_total_vc [comparison, address, step, ← hmid, hcmp,
      Word.one_ne_zero hw, Nat.ne_of_gt hw, registers.base_ne_mid, registers.key_ne_mid]
    exact addressSafe

/-- An active iteration preserves the shared search invariant and halves its
interval. This is a functional fact about the actual safe successor state. -/
theorem iteration_total (registers : Registers) {heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} {original : State w} (hw : 2 ≤ w)
    (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    TotalRelContract program heapLimit depth (body registers)
      (fun s => Invariant registers heapLimit base key xs original s ∧
        s.eval (condition registers) ≠ 0)
      (fun s t => Invariant registers heapLimit base key xs original t ∧
        (t.regs registers.hi).toNat - (t.regs registers.lo).toNat ≤
          ((s.regs registers.hi).toNat - (s.regs registers.lo).toNat) / 2) := by
  rintro s ⟨invariant, nonzero⟩
  obtain ⟨within, _⟩ := search_address registers hw invariant nonzero
  obtain ⟨finish, execution, result⟩ :=
    body_total registers (program := program) (depth := depth)
      (by omega) s within s rfl
  subst finish
  exact ⟨_, execution, step_preserves registers hw sorted invariant nonzero⟩

/-- The initialized search interval terminates with the lower-bound result and
the original shared-state frame. Its variant measures progress, not runtime. -/
theorem loop_total (registers : Registers) {heapLimit depth : Nat} {program : Program}
    {base key : Word w} {xs : List (Word w)} {original : State w} (hw : 2 ≤ w)
    (sorted : xs.Pairwise (fun a b => a.toNat ≤ b.toNat)) :
    TotalContract program heapLimit depth (loop registers)
      (Invariant registers heapLimit base key xs original)
      (Post registers heapLimit base key xs original) := by
  intro s invariant
  apply Verification.TotalWP.while_variant
    (Invariant registers heapLimit base key xs original)
    (fun t => (t.regs registers.hi).toNat - (t.regs registers.lo).toNat)
  · intro t ht
    exact ⟨trivial, trivial⟩
  · intro current hcurrent nonzero
    obtain ⟨finish, execution, preserved⟩ :=
      iteration_total registers (program := program) (depth := depth)
        hw sorted current ⟨hcurrent, nonzero⟩
    refine ⟨_, execution, preserved.1, ?_⟩
    have order := condition_positive registers hcurrent nonzero
    have shorter := Nat.div_lt_self
      (show 0 < (current.regs registers.hi).toNat -
        (current.regs registers.lo).toNat by omega) (by decide : 1 < 2)
    exact lt_of_le_of_lt preserved.2 shorter
  · exact invariant
  · intro finish hfinish zero
    exact Invariant.exit (registers := registers) (by omega) hfinish zero

end Ram.Source.Array.Search
