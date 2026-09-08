/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Total

/-!
# Ordinary logical reasoning about total program results

Separate functional properties of a deterministic program describe the same
final state. These rules let clients combine model assertions without exposing
executions. Existential ghost objects and inhabited families of properties
move through total weakest preconditions. An empty family does not supply
termination, so the universal rule explicitly requires a nonempty index type.
-/

namespace Ram.Source.Verification.TotalWP

universe u

variable {w heapLimit depth : Nat} {program : Program} {stmt : Stmt} {s : State w}
variable {P Q : State w → Prop}

/-- Two independently proved properties hold at the same actual final state. -/
theorem and (hp : TotalWP program heapLimit depth stmt P s)
    (hq : TotalWP program heapLimit depth stmt Q s) :
    TotalWP program heapLimit depth stmt (fun t => P t ∧ Q t) s := by
  obtain ⟨t, ht, hpt⟩ := hp
  obtain ⟨u, hu, hqu⟩ := hq
  have same := ht.deterministic hu
  subst u
  exact ⟨t, ht, hpt, hqu⟩

theorem and_iff :
    TotalWP program heapLimit depth stmt (fun t => P t ∧ Q t) s ↔
      TotalWP program heapLimit depth stmt P s ∧ TotalWP program heapLimit depth stmt Q s :=
  ⟨fun h => ⟨h.mono_post (fun _ hp => hp.1), h.mono_post (fun _ hp => hp.2)⟩,
    fun h => h.1.and h.2⟩

/-- Ghost witnesses belong in ordinary mathematical logic, not machine state. -/
theorem exists_iff {ι : Sort u} {post : ι → State w → Prop} :
    TotalWP program heapLimit depth stmt (fun t => ∃ i, post i t) s ↔
      ∃ i, TotalWP program heapLimit depth stmt (post i) s := by
  constructor
  · rintro ⟨t, execution, i, hp⟩
    exact ⟨i, t, execution, hp⟩
  · rintro ⟨i, t, execution, hp⟩
    exact ⟨t, execution, i, hp⟩

/-- Inhabited families of independently proved properties describe one run.
The nonempty premise is essential for total correctness. -/
theorem forall_iff {ι : Sort u} [Nonempty ι] {post : ι → State w → Prop} :
    TotalWP program heapLimit depth stmt (fun t => ∀ i, post i t) s ↔
      ∀ i, TotalWP program heapLimit depth stmt (post i) s := by
  constructor
  · intro h i
    exact h.mono_post (fun _ hp => hp i)
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨t, execution, _⟩ := h i
    refine ⟨t, execution, ?_⟩
    intro j
    obtain ⟨u, other, hp⟩ := h j
    have same := execution.deterministic other
    subst u
    exact hp

theorem congr_post (equal : ∀ t, P t ↔ Q t) :
    TotalWP program heapLimit depth stmt P s ↔ TotalWP program heapLimit depth stmt Q s :=
  ⟨fun h => h.mono_post (fun t hp => (equal t).mp hp),
    fun h => h.mono_post (fun t hq => (equal t).mpr hq)⟩

end Ram.Source.Verification.TotalWP

namespace Ram.Source

/-- Prove two model properties separately, then retain both in one contract. -/
theorem TotalContract.and {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P Q R : State w → Prop}
    (first : TotalContract program heapLimit depth stmt P Q)
    (second : TotalContract program heapLimit depth stmt P R) :
    TotalContract program heapLimit depth stmt P (fun t => Q t ∧ R t) :=
  fun s hs => Verification.TotalWP.and (first s hs) (second s hs)

theorem TotalRelContract.and {heapLimit depth : Nat} {program : Program} {stmt : Stmt}
    {P : State w → Prop} {Q R : State w → State w → Prop}
    (first : TotalRelContract program heapLimit depth stmt P Q)
    (second : TotalRelContract program heapLimit depth stmt P R) :
    TotalRelContract program heapLimit depth stmt P (fun s t => Q s t ∧ R s t) :=
  fun s hs => Verification.TotalWP.and (first s hs) (second s hs)

end Ram.Source
