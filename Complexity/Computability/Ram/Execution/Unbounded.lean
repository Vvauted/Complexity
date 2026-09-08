/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Execution.Runner

/-!
# Executable runs without a prescribed step limit

`Ram.runUntil` repeatedly uses the existing machine transition until halt, fault
or an invalid program counter. It retains the same exact transition count and
stopping reasons as `Ram.run`, without requesting an operational budget.

The implementation uses Lean's `partial_fixpoint`: it is executable and has
proved unfolding equations. A divergent execution keeps running; the logical
value `none` represents the least fixed point, not a runtime report detecting
divergence. Every returned `some` is related to a finite bounded run below.
Correctness proofs can instead supply a terminating `Ram.Exec` directly.
-/

namespace Ram

namespace Runner

/-- Tail-recursive execution using the existing successor and status functions.
`count` records transitions already performed. No step limit is selected. -/
def loopUntil (next : σ → Option σ) (status : σ → Status)
    (count : Nat) (s : σ) : Option (RunResult σ) :=
  match status s with
  | .halted => some ⟨s, count, .halted⟩
  | .fault => some ⟨s, count, .fault⟩
  | .running =>
    match next s with
    | none => some ⟨s, count, .invalidPC⟩
    | some t => loopUntil next status (count + 1) t
partial_fixpoint

/-- A backend-independent executable runner without an operational step limit. -/
def runUntilWith (next : σ → Option σ) (status : σ → Status)
    (s : σ) : Option (RunResult σ) :=
  loopUntil next status 0 s

/-- Any bounded run that actually stops is the result of the unbounded runner. -/
theorem loopUntil_of_loop (next : σ → Option σ) (status : σ → Status)
    (fuel count : Nat) (s : σ)
    (stop : (loop next status fuel count s).reason ≠ .outOfFuel) :
    loopUntil next status count s = some (loop next status fuel count s) := by
  induction fuel generalizing count s with
  | zero =>
    cases hs : status s with
    | halted => rw [loopUntil.eq_def]; simp [loop, hs]
    | fault => rw [loopUntil.eq_def]; simp [loop, hs]
    | running => simp [loop, hs] at stop
  | succ fuel ih =>
    cases hs : status s with
    | halted => rw [loopUntil.eq_def]; simp [loop, hs]
    | fault => rw [loopUntil.eq_def]; simp [loop, hs]
    | running =>
      cases hn : next s with
      | none => rw [loopUntil.eq_def]; simp [loop, hs, hn]
      | some t =>
        have tail := ih (count + 1) t (by simpa [loop, hs, hn] using stop)
        rw [loopUntil.eq_def]
        simpa [loop, hs, hn] using tail

theorem runUntilWith_of_runWith (next : σ → Option σ) (status : σ → Status)
    (fuel : Nat) (s : σ) (stop : (runWith next status fuel s).reason ≠ .outOfFuel) :
    runUntilWith next status s = some (runWith next status fuel s) :=
  loopUntil_of_loop next status fuel 0 s stop

/-- A returned result has a finite execution witness. This direction uses the
least-fixed-point induction principle, not an assumed termination argument. -/
theorem loopUntil_has_finite_run (next : σ → Option σ) (status : σ → Status)
    (count : Nat) (s : σ) (result : RunResult σ)
    (h : loopUntil next status count s = some result) :
    ∃ fuel, loop next status fuel count s = result ∧ result.reason ≠ .outOfFuel := by
  refine loopUntil.partial_correctness
    (next := next) (status := status)
    (motive := fun count s result =>
      ∃ fuel, loop next status fuel count s = result ∧ result.reason ≠ .outOfFuel)
    ?_ count s result h
  intro recur ih count s result returned
  cases hs : status s with
  | halted =>
    simp only [hs] at returned
    cases Option.some.inj returned
    exact ⟨0, by simp [loop, hs], by simp⟩
  | fault =>
    simp only [hs] at returned
    cases Option.some.inj returned
    exact ⟨0, by simp [loop, hs], by simp⟩
  | running =>
    cases hn : next s with
    | none =>
      simp only [hs, hn] at returned
      cases Option.some.inj returned
      exact ⟨1, by simp [loop, hs, hn], by simp⟩
    | some t =>
      simp only [hs, hn] at returned
      obtain ⟨fuel, hfuel, stop⟩ := ih (count + 1) t result returned
      exact ⟨fuel + 1, by simpa [loop, hs, hn] using hfuel, stop⟩

theorem loopUntil_eq_some_iff (next : σ → Option σ) (status : σ → Status)
    (count : Nat) (s : σ) (result : RunResult σ) :
    loopUntil next status count s = some result ↔
      ∃ fuel, loop next status fuel count s = result ∧ result.reason ≠ .outOfFuel := by
  constructor
  · exact loopUntil_has_finite_run next status count s result
  · rintro ⟨fuel, hfuel, stop⟩
    simpa only [hfuel] using loopUntil_of_loop next status fuel count s
      (by simpa only [hfuel] using stop)

/-- The unbounded and bounded drivers agree on all finite outcomes, including
faults and invalid program counters. Neither reports divergence as a fault. -/
theorem runUntilWith_eq_some_iff (next : σ → Option σ) (status : σ → Status)
    (s : σ) (result : RunResult σ) :
    runUntilWith next status s = some result ↔
      ∃ fuel, runWith next status fuel s = result ∧ result.reason ≠ .outOfFuel :=
  loopUntil_eq_some_iff next status 0 s result

end Runner

/-- Execute actual machine transitions until the machine stops. Divergent
programs keep running; the logical `none` is not a computable divergence test. -/
def runUntil (code : Code) (s : State w) : Option (RunResult (State w)) :=
  Runner.runUntilWith (step code) State.status s

/-- A finite outcome of the existing bounded runner is unchanged without its limit. -/
theorem runUntil_of_run {code : Code} {fuel : Nat} {s : State w}
    (stop : (run code fuel s).reason ≠ .outOfFuel) :
    runUntil code s = some (run code fuel s) :=
  Runner.runUntilWith_of_runWith (step code) State.status fuel s stop

/-- A terminating execution gives the executable result and exact count,
without requiring the user to propose an instruction budget. -/
theorem runUntil_of_exec {code : Code} {n : Nat} {s t : State w}
    (execution : Exec code n s t) (halted : t.status = .halted) :
    runUntil code s = some ⟨t, n, .halted⟩ := by
  have bounded := run_of_exec execution halted (Nat.le_refl n)
  have stop : (run code n s).reason ≠ .outOfFuel := by
    rw [bounded]
    simp
  rw [runUntil_of_run stop, bounded]

/-- All returned outcomes have a finite bounded-run witness. -/
theorem runUntil_eq_some_iff {code : Code} {s : State w} {result : RunResult (State w)} :
    runUntil code s = some result ↔
      ∃ fuel, run code fuel s = result ∧ result.reason ≠ .outOfFuel :=
  Runner.runUntilWith_eq_some_iff (step code) State.status s result

/-- Returned outcomes have an actual transition trace and the reported terminal
condition; the unbounded runner cannot return `outOfFuel`. -/
theorem runUntil_sound {code : Code} {s : State w} {result : RunResult (State w)}
    (h : runUntil code s = some result) :
    Exec code result.steps s result.state ∧ result.reason ≠ .outOfFuel ∧
      Runner.Outcome (step code) State.status result.steps result := by
  obtain ⟨fuel, bounded, stop⟩ := runUntil_eq_some_iff.mp h
  have execution := run_exec code fuel s
  have outcome := run_outcome code fuel s
  rw [bounded] at execution outcome
  refine ⟨execution.2, stop, ?_⟩
  cases hr : result.reason <;> simp_all [Runner.Outcome]

/-- A successful unbounded run is exactly a finite halted machine execution,
with the same final state and exact transition count in both directions. -/
theorem runUntil_halted_iff {code : Code} {n : Nat} {s t : State w} :
    runUntil code s = some ⟨t, n, .halted⟩ ↔ Exec code n s t ∧ t.status = .halted := by
  constructor
  · intro h
    have sound := runUntil_sound h
    exact ⟨sound.1, sound.2.2⟩
  · rintro ⟨execution, halted⟩
    exact runUntil_of_exec execution halted

end Ram
