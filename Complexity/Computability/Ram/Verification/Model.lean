/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Logic
import Complexity.Computability.Ram.Verification.Refinement
import Mathlib.Logic.Relator

/-!
# Changing and combining ordinary mathematical models

Representation relations need not be bijections. `Refines.transfer` uses
mathlib's `Relator.LiftFun` to reuse a functional theorem across related models,
including lossy projections and quotients. The input representation supplies
an actual related representative; the output relation must respect the pure
computation. Thus forgetting list order or duplicate counts does not silently
change the implemented specification.

`Refines.prod` combines observations of the same final state. It is not parallel
execution, and it does not claim disjoint ownership of memory.
-/

namespace Ram.Source.Refines

variable {α β γ δ : Type*} {program : Program} {heapLimit depth : Nat} {stmt : Stmt}
variable {inputRep : α → State w → Prop} {outputRep : β → State w → Prop} {f : α → β}

/-- Transfer an implementation along relations already used by mathematical
library proofs. A new input must have a represented old input, and the pure
functions must respect the relation in mathlib's standard sense. -/
theorem transfer {newInput : γ → State w → Prop} {newOutput : δ → State w → Prop}
    {g : γ → δ} {inputRel : α → γ → Prop} {outputRel : β → δ → Prop}
    (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (inputs : ∀ x s, newInput x s → ∃ old, inputRep old s ∧ inputRel old x)
    (outputs : ∀ y z t, outputRel y z → outputRep y t → newOutput z t)
    (functions : Relator.LiftFun inputRel outputRel f g) :
    Refines program heapLimit depth stmt newInput newOutput g := by
  intro x s hs
  obtain ⟨old, represented, related⟩ := inputs x s hs
  obtain ⟨t, execution, ht⟩ := h old s represented
  exact ⟨t, execution, outputs (f old) (g x) t (functions related) ht⟩

/-- Change an output observation by an ordinary pure function. This covers
sets, multisets, encodings and projections without a new RAM operation. -/
theorem map_output {newOutput : γ → State w → Prop} (g : β → γ)
    (h : Refines program heapLimit depth stmt inputRep outputRep f)
    (sound : ∀ y t, outputRep y t → newOutput (g y) t) :
    Refines program heapLimit depth stmt inputRep newOutput (g ∘ f) := by
  intro x
  exact (h x).mono_post (fun t ht => sound (f x) t ht)

/-- Reparameterize a specification without changing the executable program. -/
theorem comap_input (g : γ → α)
    (h : Refines program heapLimit depth stmt inputRep outputRep f) :
    Refines program heapLimit depth stmt (fun x => inputRep (g x)) outputRep (f ∘ g) :=
  fun x => h (g x)

/-- Combine independently proved observations using the standard product.
Determinism makes both assertions refer to one final state, not two runs. -/
theorem prod {otherRep : γ → State w → Prop} {g : α → γ}
    (first : Refines program heapLimit depth stmt inputRep outputRep f)
    (second : Refines program heapLimit depth stmt inputRep otherRep g) :
    Refines program heapLimit depth stmt inputRep
      (fun (result : β × γ) t => outputRep result.1 t ∧ otherRep result.2 t)
      (fun x => (f x, g x)) :=
  fun x => (first x).and (second x)

/-- Reuse an ordinary relational contract whose observations already express
the pure functional equation. There is no separate execution proof to write. -/
theorem of_observations {pre : State w → Prop} (input : State w → α)
    (output : State w → β)
    (h : TotalRelContract program heapLimit depth stmt pre
      (fun s t => output t = f (input s))) :
    Refines program heapLimit depth stmt
      (fun x s => pre s ∧ input s = x) (fun y t => output t = y) f := by
  intro x s hs
  obtain ⟨t, execution, result⟩ := h s hs.1
  exact ⟨t, execution, by simpa only [hs.2] using result⟩

end Ram.Source.Refines
