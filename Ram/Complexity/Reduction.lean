/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Component.Composition

/-!
# Executable polynomial-time many-one reductions

A `PolyTimeReduction A B D E L K` transforms instances of `L` into instances
of `K` using a fixed verified RAM component. Its input and output interfaces,
legal domains, and languages are parameters. The component supplies total
execution, polynomial time, and polynomial output size, not just an uncharged
Lean function computing the transformation.

## Main declarations

- `PolyTimeReduction.id`: the identity reduction on a shared interface.
- `PolyTimeReduction.comp`: composition by linking the executable components.
- `PolyTimeReduction.pullback`: reuse a target algorithm after the reduction.
- `PolyTimeReduction.pullbackDecider`: a target decision algorithm yields a
  source decision algorithm, together with its language-correctness proof.

These are word-RAM reductions for the specified representations and domains.
The compiled programs retain the explicit word-width and capacity conditions
of `PolyTimeComponent.runs_polynomial`. No correspondence with a Turing-machine
complexity class is asserted.
-/

namespace Ram

universe u v z

/-- A many-one reduction implemented by a polynomial-time RAM component.
The same word width is used on both sides of the domain-preservation claim. -/
structure PolyTimeReduction {α : Type u} {β : Type v}
    (A : Interface α) (B : Interface β)
    (D : Nat → α → Prop) (E : Nat → β → Prop)
    (L : α → Prop) (K : β → Prop) where
  /-- The mathematical instance transformation computed by the program. -/
  transform : α → β
  /-- Its executable implementation, with correctness and polynomial bounds. -/
  computation : PolyTimeComponent A B transform D
  /-- A legal source instance becomes a legal target instance at the same width. -/
  maps_domain : ∀ w x, D w x → E w (transform x)
  /-- Both positive and negative instances are preserved on the source domain. -/
  correct : ∀ w x, D w x → (L x ↔ K (transform x))

namespace PolyTimeReduction

variable {α : Type u} {β : Type v} {γ : Type z}
variable {A : Interface α} {B : Interface β} {C : Interface γ}
variable {D : Nat → α → Prop} {E : Nat → β → Prop} {F : Nat → γ → Prop}
variable {L : α → Prop} {K : β → Prop} {M : γ → Prop}

/-- Identity performs no body instructions and preserves the same representation. -/
def id (A : Interface α) (D : Nat → α → Prop) (L : α → Prop) :
    PolyTimeReduction A A D D L L where
  transform := fun x => x
  computation := PolyTimeComponent.id A D
  maps_domain _ _ hx := hx
  correct _ _ _ := Iff.rfl

@[simp] theorem id_transform (A : Interface α) (D : Nat → α → Prop)
    (L : α → Prop) (x : α) : (id A D L).transform x = x := rfl

/-- Compose reductions across the fixed common interface and target domain.
As in `Function.comp`, the second reduction is the first argument. -/
def comp (q : PolyTimeReduction B C E F K M)
    (p : PolyTimeReduction A B D E L K) : PolyTimeReduction A C D F L M where
  transform := q.transform ∘ p.transform
  computation := q.computation.comp p.computation p.maps_domain
  maps_domain w x hx := q.maps_domain w (p.transform x) (p.maps_domain w x hx)
  correct w x hx := (p.correct w x hx).trans
    (q.correct w (p.transform x) (p.maps_domain w x hx))

@[simp] theorem comp_transform (q : PolyTimeReduction B C E F K M)
    (p : PolyTimeReduction A B D E L K) (x : α) :
    (q.comp p).transform x = q.transform (p.transform x) := rfl

/-- Compose in forward reading order: first `p`, then `q`. -/
def trans (p : PolyTimeReduction A B D E L K)
    (q : PolyTimeReduction B C E F K M) : PolyTimeReduction A C D F L M :=
  q.comp p

@[simp] theorem trans_transform (p : PolyTimeReduction A B D E L K)
    (q : PolyTimeReduction B C E F K M) (x : α) :
    (p.trans q).transform x = q.transform (p.transform x) := rfl

/-- Reuse any polynomial-time target computation on the transformed input.
This links the programs in their shared state; it does not restart the target
with a freshly computed host-side input. -/
def pullback (r : PolyTimeReduction A B D E L K) {g : β → γ}
    (q : PolyTimeComponent B C g E) :
    PolyTimeComponent A C (g ∘ r.transform) D :=
  q.comp r.computation r.maps_domain

/-- A target Boolean decision algorithm gives an executable source decision
algorithm. The returned value contains the linked polynomial-time component;
its attached proof establishes the source-language decision specification.
The caller fixes the Boolean output interface and supplies the target's
decision proof, so neither a representation nor a decision step is free. -/
def pullbackDecider (r : PolyTimeReduction A B D E L K)
    {answer : Interface Bool} {decideTarget : β → Bool}
    (q : PolyTimeComponent B answer decideTarget E)
    (hq : ∀ w y, E w y → (K y ↔ decideTarget y = Bool.true)) :
    {_computation : PolyTimeComponent A answer (decideTarget ∘ r.transform) D //
      ∀ w x, D w x → (L x ↔ decideTarget (r.transform x) = Bool.true)} :=
  ⟨r.pullback q, fun w x hx =>
    (r.correct w x hx).trans (hq w (r.transform x) (r.maps_domain w x hx))⟩

end PolyTimeReduction

end Ram
