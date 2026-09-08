/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Memory.Frame
import Complexity.Computability.Ram.Verification.Refinement

/-!
# Retaining other mathematical objects through a refinement

A verified implementation may be used in a larger mathematical workspace.
`Refines.frame_heap` retains an arbitrary heap model alongside its result,
provided the model depends only on cells disjoint from the implementation's
proved endpoint effect. Models and footprints can depend on ordinary ghost
values; they do not generate source statements or impose an ownership type.

The proof reuses `TotalRelContract.frame_heap` for the same safe execution.
The frame is an endpoint property, not an assertion that all intermediate
states leave the framed cells unchanged.
-/

namespace Ram.Source.Refines

variable {α β γ : Type*} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : α → State w → Prop} {outputRep : β → State w → Prop} {f : α → β}

/-- Lift an implementation to a workspace containing an unrelated heap object.
Both objects retain their ordinary model types, and disjointness is a standard
mathlib proposition required only for the particular represented input pair. -/
theorem frame_heap (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (observed : γ → Set (Word w)) (writes : α → Set (Word w))
    (model : γ → (Word w → Word w) → Prop)
    (depends : ∀ z before after, Set.EqOn after before (observed z) →
      model z before → model z after)
    (unchanged : ∀ x entry finish, inputRep x entry →
      SafeExec program heapLimit depth stmt entry finish → outputRep (f x) finish →
      Set.EqOn finish.mem entry.mem (writes x)ᶜ) :
    Refines program heapLimit depth stmt
      (fun (x, z) s => inputRep x s ∧ model z s.mem ∧ Disjoint (observed z) (writes x))
      (fun (y, z) t => outputRep y t ∧ model z t.mem)
      (fun (x, z) => (f x, z)) := by
  rintro ⟨x, z⟩ entry ⟨represented, framed, disjoint⟩
  have contract : TotalRelContract program heapLimit depth stmt (inputRep x)
      (fun _ finish => outputRep (f x) finish) := h x
  exact (contract.frame_heap (observed z) (writes x) (model z) (depends z)
    disjoint (unchanged x)) entry ⟨represented, framed⟩

end Ram.Source.Refines
