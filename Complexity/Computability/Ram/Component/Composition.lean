/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Asymptotics.Polynomial
import Complexity.Computability.Ram.Component.Basic
import Complexity.Computability.Ram.Source.Linking

/-!
# Composition of verified algorithms

`Component.comp q p` first executes `p`, then `q`, using their common data
interface. It links their independent function tables, relocating every call
in the second module, including recursive calls. Both existing execution
proofs are transported without changing their instruction counts.

The intermediate-size guarantee substitutes into the second resource bound.
Prefix maxima make that substitution valid even for nonmonotone bounds.
These maxima are proof budgets, not extra instructions in the RAM program.

## Main results

- `Component.comp`: executable composition with correctness and resource bounds.
- `Component.comp_time_polynomial`: polynomial time is preserved when the first
  output has polynomial size.
- `PolyTimeComponent.comp`: reusable polynomial-time and output-size certificates.
- `PolyTimeComponent.runs_polynomial`: the resulting bound on a halted RAM run.

There is no free conversion between different encodings, no restart with a
fresh host-created state, and no concatenation of already halted binaries.
An encoding adapter is an ordinary verified component with its own cost.
-/

namespace Ram

universe u v z

namespace Component

variable {α : Type u} {β : Type v} {γ : Type z}
variable {A : Interface α} {B : Interface β} {C : Interface γ}
variable {f : α → β} {g : β → γ}
variable {D : Nat → α → Prop} {E : Nat → β → Prop}

/-- Compose independently verified modules across a shared data interface.
The second component is the first argument, as in `Function.comp`. -/
def comp (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) : Component A C (g ∘ f) D where
  locals := max p.locals q.locals
  functions := Program.link p.functions q.functions
  body := .seq p.body (q.body.renameCalls (fun i => p.functions.length + i))
  valid := Compiler.Valid.link p.valid q.valid
  timeBound n := p.timeBound n + Asymptotics.monotoneHull q.timeBound (p.sizeBound n)
  heapBound n := max (p.heapBound n) (Asymptotics.monotoneHull q.heapBound (p.sizeBound n))
  depthBound n := max (p.depthBound n) (Asymptotics.monotoneHull q.depthBound (p.sizeBound n))
  sizeBound n := Asymptotics.monotoneHull q.sizeBound (p.sizeBound n)
  size_le w x hx := Nat.le_trans (q.size_le w (f x) (hdom w x hx))
    (Nat.le_trans (Asymptotics.le_monotoneHull q.sizeBound _) (Asymptotics.hull_monotone _ (p.size_le w x hx)))
  correct x hx s hs H d hH hd := by
    obtain ⟨np, middle, hp, hm, hnp⟩ := p.correct x hx s hs H d
      (Nat.le_trans (Nat.le_max_left _ _) hH)
      (Nat.le_trans (Nat.le_max_left _ _) hd)
    have hsize := p.size_le _ x hx
    have hhq : q.heapBound (B.size (f x)) ≤ H :=
      Nat.le_trans (Asymptotics.le_monotoneHull _ _) (Nat.le_trans (Asymptotics.hull_monotone _ hsize)
        (Nat.le_trans (Nat.le_max_right _ _) hH))
    have hdq : q.depthBound (B.size (f x)) ≤ d :=
      Nat.le_trans (Asymptotics.le_monotoneHull _ _) (Nat.le_trans (Asymptotics.hull_monotone _ hsize)
        (Nat.le_trans (Nat.le_max_right _ _) hd))
    obtain ⟨nq, t, hq, ht, hnq⟩ := q.correct (f x) (hdom _ x hx) middle hm H d hhq hdq
    have hp' := hp.renameCalls_rebase (Program.embeds_link_left p.functions q.functions)
      (max p.locals q.locals)
    have hq' := hq.renameCalls_rebase (Program.embeds_link_right p.functions q.functions)
      (max p.locals q.locals)
    rw [Stmt.renameCalls_id] at hp'
    refine ⟨np + nq, t, .seq hp' hq', ht, ?_⟩
    exact Nat.add_le_add hnp (Nat.le_trans hnq
      (Nat.le_trans (Asymptotics.le_monotoneHull _ _) (Asymptotics.hull_monotone _ hsize)))

@[simp] theorem comp_timeBound (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) (n : Nat) :
    (q.comp p hdom).timeBound n =
      p.timeBound n + Asymptotics.monotoneHull q.timeBound (p.sizeBound n) := rfl

@[simp] theorem comp_sizeBound (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) (n : Nat) :
    (q.comp p hdom).sizeBound n = Asymptotics.monotoneHull q.sizeBound (p.sizeBound n) := rfl

/-- Sequential composition reuses the same heap capacity rather than summing
two disjoint artificial heaps. Extra live data belongs in the shared interface. -/
@[simp] theorem comp_heapBound (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) (n : Nat) :
    (q.comp p hdom).heapBound n =
      max (p.heapBound n) (Asymptotics.monotoneHull q.heapBound (p.sizeBound n)) := rfl

/-- Sequential calls are not nested across the module boundary. -/
@[simp] theorem comp_depthBound (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) (n : Nat) :
    (q.comp p hdom).depthBound n =
      max (p.depthBound n) (Asymptotics.monotoneHull q.depthBound (p.sizeBound n)) := rfl

/-- The compiled composite pays its prologue and halt once, not once per module. -/
theorem comp_totalTime (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) (n : Nat) :
    (q.comp p hdom).totalTime n =
      p.timeBound n + Asymptotics.monotoneHull q.timeBound (p.sizeBound n) + 2 := rfl

theorem totalTime_polynomial (p : Component A B f D)
    (ht : Asymptotics.IsPolynomiallyBounded p.timeBound) : Asymptotics.IsPolynomiallyBounded p.totalTime :=
  ht.add (Asymptotics.IsPolynomiallyBounded.const 2)

/-- The intermediate output-size bound is essential to polynomial-time closure. -/
theorem comp_time_polynomial (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x))
    (hp : Asymptotics.IsPolynomiallyBounded p.timeBound) (hq : Asymptotics.IsPolynomiallyBounded q.timeBound)
    (hs : Asymptotics.IsPolynomiallyBounded p.sizeBound) :
    Asymptotics.IsPolynomiallyBounded (q.comp p hdom).timeBound := hp.add (hq.monotoneHull.comp hs)

theorem comp_size_polynomial (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x))
    (hp : Asymptotics.IsPolynomiallyBounded p.sizeBound) (hq : Asymptotics.IsPolynomiallyBounded q.sizeBound) :
    Asymptotics.IsPolynomiallyBounded (q.comp p hdom).sizeBound := hq.monotoneHull.comp hp

/-- Polynomial capacity bounds, when supplied, also survive composition. -/
theorem comp_heap_polynomial (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x))
    (hp : Asymptotics.IsPolynomiallyBounded p.heapBound) (hq : Asymptotics.IsPolynomiallyBounded q.heapBound)
    (hs : Asymptotics.IsPolynomiallyBounded p.sizeBound) :
    Asymptotics.IsPolynomiallyBounded (q.comp p hdom).heapBound := hp.max (hq.monotoneHull.comp hs)

theorem comp_depth_polynomial (q : Component B C g E) (p : Component A B f D)
    (hdom : ∀ w x, D w x → E w (f x))
    (hp : Asymptotics.IsPolynomiallyBounded p.depthBound) (hq : Asymptotics.IsPolynomiallyBounded q.depthBound)
    (hs : Asymptotics.IsPolynomiallyBounded p.sizeBound) :
    Asymptotics.IsPolynomiallyBounded (q.comp p hdom).depthBound := hp.max (hq.monotoneHull.comp hs)

end Component

/-- A verified component with polynomial time and polynomial output size.
Capacity and word-fit conditions remain explicit when obtaining a machine run;
this structure does not assert a Turing-machine complexity-class membership. -/
structure PolyTimeComponent {α : Type u} {β : Type v}
    (A : Interface α) (B : Interface β) (f : α → β) (domain : Nat → α → Prop)
    extends Component A B f domain where
  /-- A polynomial bound on compiled body transitions. -/
  time_polynomial : Asymptotics.IsPolynomiallyBounded timeBound
  /-- A polynomial bound on the mathematical result size. -/
  size_polynomial : Asymptotics.IsPolynomiallyBounded sizeBound

namespace PolyTimeComponent

variable {α : Type u} {β : Type v} {γ : Type z}
variable {A : Interface α} {B : Interface β} {C : Interface γ}
variable {f : α → β} {g : β → γ}
variable {D : Nat → α → Prop} {E : Nat → β → Prop}

/-- Identity is polynomial-time and preserves the represented size. -/
def id (A : Interface α) (domain : Nat → α → Prop) :
    PolyTimeComponent A A (fun x => x) domain where
  toComponent := Component.id A domain
  time_polynomial := Asymptotics.IsPolynomiallyBounded.const 0
  size_polynomial := Asymptotics.IsPolynomiallyBounded.id

/-- Compose two polynomial-time certificates, including their executable modules. -/
def comp (q : PolyTimeComponent B C g E) (p : PolyTimeComponent A B f D)
    (hdom : ∀ w x, D w x → E w (f x)) : PolyTimeComponent A C (g ∘ f) D where
  toComponent := q.toComponent.comp p.toComponent hdom
  time_polynomial := Component.comp_time_polynomial _ _ _
    p.time_polynomial q.time_polynomial p.size_polynomial
  size_polynomial := Component.comp_size_polynomial _ _ _ p.size_polynomial q.size_polynomial

/-- The certificate bounds a complete halted machine execution, uniformly in
the word width and legal input, whenever the stated code and capacity fit. -/
theorem runs_polynomial (p : PolyTimeComponent A B f D) :
    ∃ c k : Nat, 0 < c ∧ ∀ (w : Nat) (x : α), D w x →
      ∀ input : List (Word w), A.represents w x (Source.State.initial input) →
      p.toComponent.code.length < 2 ^ w → p.toComponent.capacity (A.size x) < 2 ^ w →
      ∃ sourceFinal targetFinal,
        B.represents w (f x) sourceFinal ∧
        TerminatesWithin p.toComponent.code (c * (A.size x + 1) ^ k)
          (State.initial (BitVec.ofNat w (p.heapBound (A.size x)) :: input)) targetFinal ∧
        HeapEqBelow (p.heapBound (A.size x)) sourceFinal.mem targetFinal.mem ∧
        targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  obtain ⟨c, k, hc, hb⟩ :=
    (p.toComponent.totalTime_polynomial p.time_polynomial).exists_pos
  refine ⟨c, k, hc, ?_⟩
  intro w x hx input hi hcode hcapacity
  obtain ⟨s, t, hr, he, hm, ho, hin⟩ := p.toComponent.runs x hx input hi hcode hcapacity
  exact ⟨s, t, hr, he.mono (hb _), hm, ho, hin⟩

end PolyTimeComponent
end Ram
