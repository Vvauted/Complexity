/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Component.TimeBound

/-!
# Input-dependent resource bounds for an existing component

`ResourceBoundOn` refines time, heap capacity and call-depth requirements for
the same fixed component. A refinement supplies actual measured executions at
every sufficiently large capacity; the old scalar bounds alone do not justify
smaller resource requirements.

Sequential composition evaluates the second envelopes at the actual first
result. Heap and depth combine by maximum, while time adds. The compiled code
is unchanged by a refinement; its input header uses the refined heap bound.
The resulting address-capacity envelope includes the compiler's sufficient
stack reservation. It is not a count of live or allocated memory words.
-/

namespace Ram.Component

universe u v z

variable {α : Type u} {β : Type v} {γ : Type z}
variable {A : Interface α} {B : Interface β} {C : Interface γ}
variable {f : α → β} {g : β → γ} {D : Nat → α → Prop} {E : Nat → β → Prop}

/-- Full-input resource envelopes justified by executions of the same component.
The heap envelope is a sufficient exclusive bound on source heap addresses;
the depth envelope bounds nested calls, not their cumulative number. -/
def ResourceBoundOn (p : Component A B f D)
    (time heap depth : Nat → α → Nat) : Prop :=
  ∀ {w} x, D w x → ∀ s, A.represents w x s →
    ∀ heapLimit callDepth, heap w x ≤ heapLimit → depth w x ≤ callDepth →
      ∃ steps t,
        Source.LocalMeasuredExec p.locals p.functions heapLimit callDepth p.body steps s t ∧
        B.represents w (f x) t ∧ steps ≤ time w x

/-- The original component proof supplies its scalar resource envelopes on all
inputs. More precise heap or depth bounds require a new execution proof. -/
theorem resourceBoundOn (p : Component A B f D) :
    p.ResourceBoundOn (fun _ x => p.timeBound (A.size x))
      (fun _ x => p.heapBound (A.size x)) (fun _ x => p.depthBound (A.size x)) :=
  p.correct

namespace ResourceBoundOn

variable {p : Component A B f D}
variable {time heap depth time' heap' depth' : Nat → α → Nat}

/-- An existing time refinement retains exactly its original heap and depth
requirements; this conversion does not claim any resource reduction. -/
theorem of_timeBoundOn (h : p.TimeBoundOn time) :
    p.ResourceBoundOn time (fun _ x => p.heapBound (A.size x))
      (fun _ x => p.depthBound (A.size x)) := h

/-- Enlarge proved resource requirements and the time budget on legal inputs.
The resulting proof reuses the same execution at the requested capacities. -/
theorem mono (h : p.ResourceBoundOn time heap depth)
    (ht : ∀ w x, D w x → time w x ≤ time' w x)
    (hh : ∀ w x, D w x → heap w x ≤ heap' w x)
    (hd : ∀ w x, D w x → depth w x ≤ depth' w x) :
    p.ResourceBoundOn time' heap' depth' := by
  intro w x hx s hs H d hH hd'
  obtain ⟨steps, t, he, hr, hb⟩ := h x hx s hs H d
    ((hh w x hx).trans hH) ((hd w x hx).trans hd')
  exact ⟨steps, t, he, hr, hb.trans (ht w x hx)⟩

/-- Refined sequential envelopes depend on the actual intermediate value.
Both modules execute on the shared representation at common heap and depth
capacities, using the existing linker without changing their step counts. -/
theorem comp {q : Component B C g E}
    {secondTime secondHeap secondDepth : Nat → β → Nat}
    (second : q.ResourceBoundOn secondTime secondHeap secondDepth)
    (first : p.ResourceBoundOn time heap depth)
    (hdom : ∀ w x, D w x → E w (f x)) :
    (q.comp p hdom).ResourceBoundOn
      (fun w x => time w x + secondTime w (f x))
      (fun w x => max (heap w x) (secondHeap w (f x)))
      (fun w x => max (depth w x) (secondDepth w (f x))) := by
  intro w x hx s hs H d hH hd
  obtain ⟨np, middle, hp, hm, hnp⟩ := first x hx s hs H d
    ((Nat.le_max_left _ _).trans hH) ((Nat.le_max_left _ _).trans hd)
  obtain ⟨nq, t, hq, ht, hnq⟩ := second (f x) (hdom w x hx) middle hm H d
    ((Nat.le_max_right _ _).trans hH) ((Nat.le_max_right _ _).trans hd)
  have hp' := hp.renameCalls_rebase (Program.embeds_link_left p.functions q.functions)
    (max p.locals q.locals)
  have hq' := hq.renameCalls_rebase (Program.embeds_link_right p.functions q.functions)
    (max p.locals q.locals)
  rw [Stmt.renameCalls_id] at hp'
  exact ⟨np + nq, t, .seq hp' hq', ht, Nat.add_le_add hnp hnq⟩

/-- Reuse the refined proof in a larger source contract at any sufficient
heap capacity and call depth, preserving the component's mathematical input. -/
theorem contract (h : p.ResourceBoundOn time heap depth) {w : Nat} (x : α)
    (hx : D w x) {heapLimit callDepth : Nat}
    (hh : heap w x ≤ heapLimit) (hd : depth w x ≤ callDepth) :
    Source.Contract p.locals p.functions heapLimit callDepth p.body
      (A.represents w x) (B.represents w (f x)) (fun _ => time w x) :=
  fun s hs => h x hx s hs heapLimit callDepth hh hd

/-- Run the same compiled code with the refined heap header and resource-fit
premise. The complete run pays one header read and one halt; source input is
the actual remaining stream, not an uncharged loader. The returned observation
covers the refined source heap, local registers and I/O, not private stack words. -/
theorem runs_observed (h : p.ResourceBoundOn time heap depth) {w : Nat} (x : α)
    (hx : D w x) (input : List (Word w))
    (hinput : A.represents w x (Source.State.initial input))
    (hcode : p.code.length < 2 ^ w)
    (hcapacity : heap w x + depth w x * ABI.frameSize p.locals < 2 ^ w) :
    ∃ sourceFinal targetFinal,
      B.represents w (f x) sourceFinal ∧
      TerminatesWithin p.code (time w x + 2)
        (State.initial (BitVec.ofNat w (heap w x) :: input)) targetFinal ∧
      Source.State.Observes (heap w x) p.locals sourceFinal targetFinal :=
  (h.contract x hx le_rfl le_rfl).compile_observed p.compile_eq hcode hcapacity hinput

end ResourceBoundOn
end Ram.Component
