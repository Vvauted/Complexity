import Ram.Source
import Ram.ExprCompile

/-!
# Heap agreement and the boundary of the call stack

The source heap occupies addresses below an explicit bound. Target stack words
above that boundary must not be equated to the source heap. A source expression
is insensitive to those words when every load it actually performs is within
the heap. These are semantic proof conditions, not free runtime bounds checks.
-/

namespace Ram

def HeapEqBelow (limit : Nat) (a b : Word w → Word w) : Prop :=
  ∀ address, address.toNat < limit → a address = b address

namespace HeapEqBelow

theorem refl (limit : Nat) (mem : Word w → Word w) : HeapEqBelow limit mem mem :=
  fun _ _ => rfl

theorem symm {limit : Nat} {a b : Word w → Word w} (h : HeapEqBelow limit a b) :
    HeapEqBelow limit b a := fun address ha => (h address ha).symm

theorem trans {limit : Nat} {a b c : Word w → Word w}
    (hab : HeapEqBelow limit a b) (hbc : HeapEqBelow limit b c) :
    HeapEqBelow limit a c := fun address ha => (hab address ha).trans (hbc address ha)

/-- A target stack write cannot change the source-visible heap. -/
theorem setMem_above {limit : Nat} {mem : Word w → Word w} {s : State w}
    (h : HeapEqBelow limit mem s.mem) (address value : Word w)
    (ha : limit ≤ address.toNat) :
    HeapEqBelow limit mem (s.setMem address value).mem := by
  intro a hlt
  have hne : a ≠ address := by
    intro heq
    subst a
    omega
  rw [State.setMem_ne s address a value hne]
  exact h a hlt

end HeapEqBelow

namespace Expr

/-- Every memory read performed by this expression is in the source heap.
The condition also checks loads used to calculate another load's address. -/
def ReadsBelow (limit : Nat) (regs : Reg → Word w) (mem : Word w → Word w) :
    Expr → Prop
  | .const _ | .var _ => True
  | .bin _ a b => a.ReadsBelow limit regs mem ∧ b.ReadsBelow limit regs mem
  | .load a => a.ReadsBelow limit regs mem ∧ (a.eval regs mem).toNat < limit

/-- Agreement is needed only on source variables and accessible heap words,
not on the compiler's scratch registers or its reserved stack region. -/
theorem eval_eq_of_readsBelow {e : Expr} {locals limit : Nat}
    {r₁ r₂ : Reg → Word w} {m₁ m₂ : Word w → Word w}
    (hb : e.Bounded locals) (hs : e.ReadsBelow limit r₁ m₁)
    (hr : ∀ x, x < locals → r₁ x = r₂ x) (hm : HeapEqBelow limit m₁ m₂) :
    e.eval r₁ m₁ = e.eval r₂ m₂ := by
  induction e with
  | const => rfl
  | var x => exact hr x hb
  | bin op a b ia ib =>
      simp only [eval, ia hb.1 hs.1, ib hb.2 hs.2]
  | load a ih =>
      change m₁ (a.eval r₁ m₁) = m₂ (a.eval r₂ m₂)
      rw [hm _ hs.2, ih hb hs.1]

theorem readsBelow_congr {e : Expr} {locals limit : Nat}
    {r₁ r₂ : Reg → Word w} {m₁ m₂ : Word w → Word w}
    (hb : e.Bounded locals) (hs : e.ReadsBelow limit r₁ m₁)
    (hr : ∀ x, x < locals → r₁ x = r₂ x) (hm : HeapEqBelow limit m₁ m₂) :
    e.ReadsBelow limit r₂ m₂ := by
  induction e with
  | const => trivial
  | var => trivial
  | bin op a b ia ib => exact ⟨ia hb.1 hs.1, ib hb.2 hs.2⟩
  | load a ih =>
      refine ⟨ih hb hs.1, ?_⟩
      rw [← eval_eq_of_readsBelow (e := a) hb hs.1 hr hm]
      exact hs.2

end Expr

namespace Source.State

/-- The source-visible state relation. The target program counter, scratch
registers, and reserved stack region are intentionally not source data. -/
structure Matches (heapLimit locals : Nat) (s : Source.State w) (t : Ram.State w) : Prop where
  regs : ∀ x, x < locals → s.regs x = t.regs x
  heap : HeapEqBelow heapLimit s.mem t.mem
  input : s.input = t.input
  output : s.outputRev = t.outputRev
  running : t.status = .running

theorem Matches.eval_eq {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) {e : Expr} (hb : e.Bounded locals)
    (hs : e.ReadsBelow heapLimit s.regs s.mem) : s.eval e = e.eval t.regs t.mem :=
  Expr.eval_eq_of_readsBelow hb hs h.regs h.heap

/-- Compiling an expression preserves the source frame and computes its source
value even when the target memory also contains a private call stack. -/
theorem Matches.compile_expr {heapLimit locals scratch : Nat}
    {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) {e : Expr} (hb : e.Bounded locals)
    (hs : e.ReadsBelow heapLimit s.regs s.mem) (hfresh : locals ≤ scratch) :
    Matches heapLimit locals s (execBlock (e.compile scratch) t) ∧
      (execBlock (e.compile scratch) t).regs scratch = s.eval e := by
  have hc := Expr.compile_correct (hb.mono hfresh) t
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    exact (h.regs x hx).trans (hc.below x (Nat.lt_of_lt_of_le hx hfresh)).symm
  · rw [hc.memory]
    exact h.heap
  · exact h.input.trans hc.input.symm
  · exact h.output.trans hc.output.symm
  · exact hc.status.trans h.running
  · exact hc.value.trans (h.eval_eq hb hs).symm

end Source.State
end Ram
