/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Program.Memory
import Complexity.Computability.Ram.Component.ResourceBound

/-!
# Component correctness, time and actual heap accesses in one run

Resource bounds reach the same complete halted machine execution that returns
the component result. The address envelope covers source data and compiler
stack operations; it is sufficient capacity, not peak live allocation.
-/

namespace Ram.Component

universe u v

variable {α : Type u} {β : Type v} {A : Interface α} {B : Interface β}
variable {f : α → β} {D : Nat → α → Prop} {p : Component A B f D}
variable {time heap depth : Nat → α → Nat}

/-- A refined component proof supplies correctness, exact target execution,
its time bound and its actual address bound on one complete machine run. -/
theorem ResourceBoundOn.runs_memory (h : p.ResourceBoundOn time heap depth)
    {w : Nat} (x : α) (hx : D w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w)
    (hcapacity : heap w x + depth w x * ABI.frameSize p.locals < 2 ^ w) :
    ∃ steps sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧ steps ≤ time w x + 2 ∧
      Exec p.code steps (State.initial (BitVec.ofNat w (heap w x) :: input)) targetFinal ∧
      targetFinal.status = .halted ∧
      Source.State.Observes (heap w x) p.locals sourceFinal targetFinal ∧
      ∀ address ∈ heapAccesses p.code steps
          (State.initial (BitVec.ofNat w (heap w x) :: input)),
        address.toNat < heap w x + depth w x * ABI.frameSize p.locals := by
  obtain ⟨bodySteps, sourceFinal, hxBody, hresult, htime⟩ :=
    h x hx (Source.State.initial input) hinput (heap w x) (depth w x) le_rfl le_rfl
  obtain ⟨bodyFinish, _, hfull, hhalt, hobs⟩ :=
    LocalCompiler.compileChecked_runs_observed p.compile_eq hcode hcapacity hxBody
  exact ⟨bodySteps + 2, sourceFinal, execInstr .halt bodyFinish, hresult,
    Nat.add_le_add_right htime 2, hfull, hhalt, hobs,
    fun _ member => LocalCompiler.compileChecked_heapAccesses_below
      p.compile_eq hcode hcapacity hxBody member⟩

/-- The original scalar component envelopes also bound every actual heap
access of the complete run; no additional per-component memory proof is needed. -/
theorem runs_memory (p : Component A B f D) {w : Nat} (x : α)
    (hx : D w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w) (hcapacity : p.capacity (A.size x) < 2 ^ w) :
    ∃ steps sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧ steps ≤ p.totalTime (A.size x) ∧
      Exec p.code steps
        (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
      targetFinal.status = .halted ∧
      Source.State.Observes (p.heapBound (A.size x)) p.locals sourceFinal targetFinal ∧
      ∀ address ∈ heapAccesses p.code steps
          (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)),
        address.toNat < p.capacity (A.size x) :=
  ResourceBoundOn.runs_memory p.resourceBoundOn x hx input hinput hcode hcapacity

end Ram.Component
