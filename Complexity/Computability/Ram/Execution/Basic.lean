/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Basic

/-!
# Execution counted by machine transitions

`Exec code n s t` means exactly `n` applications of the single transition rule
take state `s` to `t`. No source operation, assertion or user annotation assigns
a cost. The executable runner is proved equivalent to this relation.
-/

namespace Ram

/-- Exactly `n` successful machine transitions. Executing a halt instruction
counts once; already halted states cannot take another transition. -/
inductive Exec (code : Code) : Nat → State w → State w → Prop where
  | refl (s) : Exec code 0 s s
  | cons {n s u t} : step code s = some u → Exec code n u t → Exec code (n + 1) s t

namespace Exec

@[simp] theorem zero_iff {code : Code} {s t : State w} :
    Exec code 0 s t ↔ s = t := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .refl s

theorem single {code : Code} {s t : State w} (h : step code s = some t) :
    Exec code 1 s t := .cons h (.refl t)

@[simp] theorem one_iff {code : Code} {s t : State w} :
    Exec code 1 s t ↔ step code s = some t := by
  constructor
  · intro h
    cases h with
    | cons hs he =>
        cases he
        exact hs
  · exact single

theorem succ_iff {code : Code} {n : Nat} {s t : State w} :
    Exec code (n + 1) s t ↔ ∃ u, step code s = some u ∧ Exec code n u t := by
  constructor
  · intro h
    cases h with
    | cons hs he => exact ⟨_, hs, he⟩
  · rintro ⟨u, hs, he⟩
    exact .cons hs he

/-- Execution segments compose; the number of actual transitions adds. -/
theorem trans {code : Code} {n m : Nat} {s u t : State w}
    (h₁ : Exec code n s u) (h₂ : Exec code m u t) : Exec code (n + m) s t := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons n s v u hs he ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Exec.cons hs (ih h₂)

theorem snoc {code : Code} {n : Nat} {s u t : State w}
    (he : Exec code n s u) (hs : step code u = some t) : Exec code (n + 1) s t :=
  he.trans (single hs)

/-- Every cut point in an execution yields two execution segments. -/
theorem split {code : Code} {n m : Nat} {s t : State w}
    (h : Exec code (n + m) s t) : ∃ u, Exec code n s u ∧ Exec code m u t := by
  induction n generalizing s with
  | zero => exact ⟨s, .refl s, by simpa using h⟩
  | succ n ih =>
      have h' : Exec code ((n + m) + 1) s t := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      obtain ⟨v, hs, hv⟩ := succ_iff.mp h'
      obtain ⟨u, hu, ht⟩ := ih hv
      exact ⟨u, .cons hs hu, ht⟩

theorem add_iff {code : Code} {n m : Nat} {s t : State w} :
    Exec code (n + m) s t ↔ ∃ u, Exec code n s u ∧ Exec code m u t := by
  constructor
  · exact split
  · rintro ⟨u, h₁, h₂⟩
    exact h₁.trans h₂

theorem deterministic {code : Code} {n : Nat} {s t u : State w}
    (ht : Exec code n s t) (hu : Exec code n s u) : t = u := by
  induction ht generalizing u with
  | refl => exact zero_iff.mp hu
  | cons hs he ih =>
      obtain ⟨v, hv, hu'⟩ := succ_iff.mp hu
      have hv_eq := step_deterministic hs hv
      cases hv_eq
      exact ih hu'

theorem eq_of_no_step {code : Code} {n : Nat} {s t : State w}
    (hs : step code s = none) (h : Exec code n s t) : n = 0 ∧ t = s := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | cons hstep _ => simp [hs] at hstep

theorem eq_of_halted {code : Code} {n : Nat} {s t : State w}
    (hs : s.status = .halted) (h : Exec code n s t) : n = 0 ∧ t = s :=
  eq_of_no_step (step_of_halted hs) h

/-- Successful termination has a unique exact transition count, not merely a
unique result for a caller-chosen count. -/
theorem terminal_unique {code : Code} {n m : Nat} {s t u : State w}
    (ht : Exec code n s t) (hu : Exec code m s u)
    (htstop : step code t = none) (hustop : step code u = none) :
    n = m ∧ t = u := by
  induction ht generalizing m u with
  | refl =>
      obtain ⟨hm, hu'⟩ := eq_of_no_step htstop hu
      exact ⟨hm.symm, hu'.symm⟩
  | @cons n s v t hs he ih =>
      cases hu with
      | refl => simp [hustop] at hs
      | @cons m _ z u hz hu' =>
          have hz_eq := step_deterministic hs hz
          cases hz_eq
          obtain ⟨hnm, htu⟩ := ih hu' htstop hustop
          exact ⟨congrArg (· + 1) hnm, htu⟩

end Exec

/-- Run for exactly `fuel` transitions. `none` means the requested number of
transitions does not exist, not that an exhausted budget establishes divergence. -/
def runExact (code : Code) : Nat → State w → Option (State w)
  | 0, s => some s
  | n + 1, s => (step code s).bind (runExact code n)

@[simp] theorem runExact_zero (code : Code) (s : State w) :
    runExact code 0 s = some s := rfl

theorem runExact_succ (code : Code) (n : Nat) (s : State w) :
    runExact code (n + 1) s = (step code s).bind (runExact code n) := rfl

theorem runExact_iff {code : Code} {n : Nat} {s t : State w} :
    runExact code n s = some t ↔ Exec code n s t := by
  induction n generalizing s with
  | zero => simp [runExact, Exec.zero_iff]
  | succ n ih =>
      rw [runExact_succ, Exec.succ_iff]
      cases step code s with
      | none => simp
      | some u => simp [ih]

theorem runExact_add (code : Code) (n m : Nat) (s : State w) :
    runExact code (n + m) s = (runExact code n s).bind (runExact code m) := by
  induction n generalizing s with
  | zero => simp [runExact]
  | succ n ih =>
      have hadd : n + 1 + m = (n + m) + 1 := by omega
      rw [hadd, runExact_succ, runExact_succ]
      cases step code s <;> simp [ih]

/-- A total, successful run with a transition bound. Faults and stuck program
counters do not satisfy this judgment. -/
def TerminatesWithin (code : Code) (bound : Nat) (s t : State w) : Prop :=
  ∃ n, n ≤ bound ∧ Exec code n s t ∧ t.status = .halted

theorem TerminatesWithin.mono {code : Code} {a b : Nat} {s t : State w}
    (h : TerminatesWithin code a s t) (hab : a ≤ b) :
    TerminatesWithin code b s t := by
  obtain ⟨n, hn, he, ht⟩ := h
  exact ⟨n, Nat.le_trans hn hab, he, ht⟩

end Ram
