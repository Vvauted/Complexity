import Ram.Execution
import Cslib.Foundations.Data.RelatesInSteps

/-!
# Exact RAM executions in CSLib's step-counting relation

This module imports the upstream CSLib definitions; it does not duplicate them.
One edge is exactly one successful `Ram.step`, including the transition into
the halted state. CSLib's bound alone does not distinguish success from faults,
so the successful-termination bridge retains the explicit halted postcondition.
-/

namespace Ram.Cslib

/-- One actual RAM transition, viewed as a relation for CSLib. -/
def transition (code : Code) : State w → State w → Prop :=
  fun s t => step code s = some t

/-- The RAM and CSLib exact judgments count precisely the same transitions. -/
theorem exec_iff_relatesInSteps {code : Code} {n : Nat} {s t : State w} :
    Exec code n s t ↔ Relation.RelatesInSteps (transition code) s t n := by
  constructor
  · intro h
    induction h with
    | refl s => exact .refl s
    | @cons n s u t hs _ ih =>
      exact Relation.RelatesInSteps.head s u t n hs ih
  · intro h
    induction h with
    | refl => exact .refl _
    | tail u t n _ hs ih => exact ih.snoc hs

/-- The executable reference runner also lands in the upstream CSLib judgment. -/
theorem runExact_iff_relatesInSteps {code : Code} {n : Nat} {s t : State w} :
    runExact code n s = some t ↔ Relation.RelatesInSteps (transition code) s t n :=
  runExact_iff.trans exec_iff_relatesInSteps

/-- A CSLib step bound plus successful termination is exactly the RAM budget
judgment. Merely being reachable within the budget is not a proof of success. -/
theorem terminatesWithin_iff_relatesWithinSteps {code : Code} {budget : Nat}
    {s t : State w} :
    TerminatesWithin code budget s t ↔
      Relation.RelatesWithinSteps (transition code) s t budget ∧ t.status = .halted := by
  constructor
  · rintro ⟨n, hn, he, hhalt⟩
    exact ⟨⟨n, hn, exec_iff_relatesInSteps.mp he⟩, hhalt⟩
  · rintro ⟨⟨n, hn, he⟩, hhalt⟩
    exact ⟨n, hn, exec_iff_relatesInSteps.mpr he, hhalt⟩

end Ram.Cslib
