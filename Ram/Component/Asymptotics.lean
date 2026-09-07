/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Component.TimeBound

/-!
# Asymptotic composition at the actual intermediate input

The legal-input map preserves word width and sends `x` to the mathematical
result `f x` of the first component. Pulling a downstream eventual bound back
along this map requires an explicit `Tendsto` proof. In particular, an
unbounded-input estimate for the second component cannot simply be applied to
a bounded intermediate family.

The certificate constructor uses the supplied realization of the composed
component: its code, encoding, admissible domain and resource requirements do
not change. Exact body bounds come from `TimeBoundOn.comp`; one header read and
one halt are included before applying ordinary mathlib `IsBigO` arithmetic.
-/

namespace Ram.Component

variable {α β : Type} {f : α → β}
variable {D : Nat → α → Prop} {E : Nat → β → Prop}

/-- The actual mathematical result of the first component, at the same word
width, together with the required legality proof for the second component. -/
def mapLegalInput (f : α → β) (hdom : ∀ w x, D w x → E w (f x)) :
    LegalInput D → LegalInput E :=
  fun i => ⟨(i.val.1, f i.val.2), hdom i.val.1 i.val.2 i.property⟩

private theorem isBigO_add_two {ι : Type} {l : Filter ι}
    {firstTime secondTime firstGrowth secondGrowth : ι → Nat}
    (first : Asymptotics.IsBigO l (fun i => (firstTime i : ℝ))
      (fun i => (firstGrowth i : ℝ)))
    (second : Asymptotics.IsBigO l (fun i => (secondTime i : ℝ))
      (fun i => (secondGrowth i : ℝ))) :
    Asymptotics.IsBigO l (fun i => ((firstTime i + secondTime i + 2 : Nat) : ℝ))
      (fun i => ((firstGrowth i + secondGrowth i + 1 : Nat) : ℝ)) := by
  have dominates (k : ι → Nat)
      (hk : ∀ i, k i ≤ firstGrowth i + secondGrowth i + 1) :
      Asymptotics.IsBigO l (fun i => (k i : ℝ))
        (fun i => ((firstGrowth i + secondGrowth i + 1 : Nat) : ℝ)) := by
    apply Asymptotics.isBigO_of_le l
    intro i
    simpa only [Real.norm_natCast] using
      (Nat.cast_le.mpr (hk i) : (k i : ℝ) ≤ (firstGrowth i + secondGrowth i + 1 : Nat))
  have hfirst := first.trans (dominates firstGrowth (fun i => by omega))
  have hsecond := second.trans (dominates secondGrowth (fun i => by omega))
  have hone : Asymptotics.IsBigO l (fun _ : ι => (1 : ℝ))
      (fun i => ((firstGrowth i + secondGrowth i + 1 : Nat) : ℝ)) := by
    simpa only [Nat.cast_one] using dominates (fun _ => 1) (by
      intro i
      change 1 ≤ firstGrowth i + secondGrowth i + 1
      omega)
  have htwo := (Asymptotics.isBigO_const_const (2 : ℝ)
    (by norm_num : (1 : ℝ) ≠ 0) l).trans hone
  simpa only [Nat.cast_add, Nat.cast_ofNat] using (hfirst.add hsecond).add htwo

/-- Combine body-time estimates at the actual intermediate value, including
the complete program's header read and halt. The downstream filter condition
is essential: eventual estimates alone say nothing about excluded small inputs. -/
theorem isBigO_comp_time
    (hdom : ∀ w x, D w x → E w (f x))
    {time : Nat → α → Nat} {secondTime : Nat → β → Nat}
    {l : Filter (LegalInput D)} {m : Filter (LegalInput E)}
    {growth : LegalInput D → Nat} {secondGrowth : LegalInput E → Nat}
    (first : Asymptotics.IsBigO l (fun i => (time i.val.1 i.val.2 : ℝ))
      (fun i => (growth i : ℝ)))
    (second : Asymptotics.IsBigO m (fun i => (secondTime i.val.1 i.val.2 : ℝ))
      (fun i => (secondGrowth i : ℝ)))
    (hmap : Filter.Tendsto (mapLegalInput f hdom) l m) :
    Asymptotics.IsBigO l
      (fun i => ((time i.val.1 i.val.2 + secondTime i.val.1 (f i.val.2) + 2 : Nat) : ℝ))
      (fun i => ((growth i + secondGrowth (mapLegalInput f hdom i) + 1 : Nat) : ℝ)) :=
  isBigO_add_two first (second.comp_tendsto hmap)

namespace Realization

universe u

variable {γ : Type u} {A : Interface α} {B : Interface β} {C : Interface γ}
variable {g : β → γ} {p : Component A B f D} {q : Component B C g E}
variable {hdom : ∀ w x, D w x → E w (f x)} {problem : Problem α}
variable {time : Nat → α → Nat} {secondTime : Nat → β → Nat}
variable {l : Filter (LegalInput problem.admissible)} [l.NeBot]
variable {m : Filter (LegalInput E)}
variable {growth : LegalInput problem.admissible → Nat} {secondGrowth : LegalInput E → Nat}

/-- Export compositional asymptotics through an existing realization of the
composed program. All legal inputs retain their original execution and answer
proofs, including inputs outside the eventual bounds. A further desired growth
bound can be supplied with `AsymptoticCertificateAt.weaken`. -/
def toCompAsymptoticCertificateAt (r : Realization (q.comp p hdom) problem)
    (first : p.TimeBoundOn time) (second : q.TimeBoundOn secondTime)
    (hfirst : Asymptotics.IsBigO l (fun i => (time i.val.1 i.val.2 : ℝ))
      (fun i => (growth i : ℝ)))
    (hsecond : Asymptotics.IsBigO m (fun i => (secondTime i.val.1 i.val.2 : ℝ))
      (fun i => (secondGrowth i : ℝ)))
    (hmap : Filter.Tendsto
      (mapLegalInput f (fun w x hx => hdom w x (r.domain_of_admissible w x hx))) l m) :
    AsymptoticCertificateAt problem l
      (fun i => growth i + secondGrowth
        (mapLegalInput f (fun w x hx => hdom w x (r.domain_of_admissible w x hx)) i) + 1) :=
  r.toAsymptoticCertificateAt (second.comp first hdom)
    (isBigO_comp_time (fun w x hx => hdom w x (r.domain_of_admissible w x hx))
      hfirst hsecond hmap)

/-- The asymptotic composition constructor retains the exact compiled module
whose representation and encoding were fixed by the supplied realization. -/
@[simp] theorem toCompAsymptoticCertificateAt_code
    (r : Realization (q.comp p hdom) problem)
    (first : p.TimeBoundOn time) (second : q.TimeBoundOn secondTime)
    (hfirst : Asymptotics.IsBigO l (fun i => (time i.val.1 i.val.2 : ℝ))
      (fun i => (growth i : ℝ)))
    (hsecond : Asymptotics.IsBigO m (fun i => (secondTime i.val.1 i.val.2 : ℝ))
      (fun i => (secondGrowth i : ℝ)))
    (hmap : Filter.Tendsto
      (mapLegalInput f (fun w x hx => hdom w x (r.domain_of_admissible w x hx))) l m) :
    (r.toCompAsymptoticCertificateAt first second hfirst hsecond hmap).code =
      (q.comp p hdom).code := rfl

end Realization
end Ram.Component
