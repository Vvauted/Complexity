/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Verification.Time
import Mathlib.Logic.Equiv.Defs

/-!
# Refinement to ordinary Lean functions

`Refines` relates a terminating safe RAM source program to a pure Lean function
through input and output representation predicates. The mathematical function
can use mathlib; it is a specification, not an executable RAM instruction.
Clients prove its mathematical properties normally and transfer them using
`Refines.spec`. The representation predicates may retain storage invariants,
word bounds, disjointness and other program-specific preconditions.

No bijection between an entire heap and an abstract value is required. Genuine
equivalences of mathematical models are reusable through `Refines.equiv`.
-/

namespace Ram.Source

/-- Safe total refinement of a RAM statement to a pure mathematical function. -/
def Refines {α β : Type*} (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (inputRep : α → State w → Prop) (outputRep : β → State w → Prop) (f : α → β) : Prop :=
  ∀ x, TotalContract program heapLimit depth stmt (inputRep x) (outputRep (f x))

namespace Refines

variable {α β γ : Type*} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : α → State w → Prop} {outputRep : β → State w → Prop} {f : α → β}

/-- A mathematical theorem about the pure function becomes a RAM postcondition.
Only this bridge uses representation assertions; the theorem itself is ordinary Lean. -/
theorem spec (h : Refines program heapLimit depth stmt inputRep outputRep f)
    {P : α → Prop} {Q : α → β → Prop} (property : ∀ x, P x → Q x (f x))
    (x : α) (hx : P x) :
    TotalContract program heapLimit depth stmt (inputRep x)
      (fun t => ∃ y, outputRep y t ∧ Q x y) := by
  intro s hs
  obtain ⟨t, execution, represented⟩ := h x s hs
  exact ⟨t, execution, f x, represented, property x hx⟩

/-- Compose implementations using their abstract functions and shared model,
without unfolding either statement's implementation. -/
theorem seq {first second : Stmt} {middleRep : β → State w → Prop}
    {finalRep : γ → State w → Prop} {g : β → γ}
    (ha : Refines program heapLimit depth first inputRep middleRep f)
    (hb : Refines program heapLimit depth second middleRep finalRep g) :
    Refines program heapLimit depth (.seq first second) inputRep finalRep (g ∘ f) := by
  intro x s hs
  obtain ⟨middle, firstExec, hm⟩ := ha x s hs
  obtain ⟨t, secondExec, ht⟩ := hb (f x) middle hm
  exact ⟨t, .seq firstExec secondExec, ht⟩

/-- A proved equality of ordinary Lean functions transports an implementation. -/
theorem congr_fun {g : α → β}
    (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (equal : ∀ x, f x = g x) :
    Refines program heapLimit depth stmt inputRep outputRep g := by
  intro x
  simpa only [equal x] using h x

/-- Use existing mathlib equivalences to change mathematical models.
This does not assert that distinct heap representations are identical. -/
theorem equiv {α' β' : Type*}
    (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (input : α ≃ α') (output : β ≃ β') :
    Refines program heapLimit depth stmt
      (fun x => inputRep (input.symm x)) (fun y => outputRep (output.symm y))
      (fun x => output (f (input.symm x))) := by
  intro x
  simpa only [Equiv.symm_apply_apply] using h (input.symm x)

/-- The result can be read through an ordinary observation function. -/
theorem observes (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (observe : State w → β) (sound : ∀ y t, outputRep y t → observe t = y) (x : α) :
    TotalContract program heapLimit depth stmt (inputRep x) (fun t => observe t = f x) := by
  intro s hs
  obtain ⟨t, execution, ht⟩ := h x s hs
  exact ⟨t, execution, sound (f x) t ht⟩

/-- Attach a separately proved actual execution bound to a refinement. -/
theorem with_timeBound {control : Nat} {bound : State w → Nat}
    (h : Refines program heapLimit depth stmt inputRep outputRep f) (x : α)
    (cost : TimeBound control program heapLimit depth stmt (inputRep x) bound) :
    Contract control program heapLimit depth stmt (inputRep x) (outputRep (f x)) bound :=
  (h x).with_timeBound cost

end Refines
end Ram.Source
