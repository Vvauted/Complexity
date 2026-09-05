import Ram.Machine

/-!
# Pure expressions of the structured language

Expressions use a fixed vocabulary and can read individual heap words. They
cannot call arbitrary Lean functions, alter the heap, or carry a cost. Their
register bound is a compiler freshness condition, not a runtime restriction on
the values they compute. Function-local variable names will elaborate to these
finite register indices.
-/

namespace Ram

inductive Expr where
  | const (value : Nat)
  | var (name : Reg)
  | bin (op : BinOp) (lhs rhs : Expr)
  | load (addr : Expr)
  deriving DecidableEq, Repr

namespace Expr

def eval (e : Expr) (regs : Reg → Word w) (mem : Word w → Word w) : Word w :=
  match e with
  | .const n => BitVec.ofNat w n
  | .var x => regs x
  | .bin op a b => op.eval (a.eval regs mem) (b.eval regs mem)
  | .load a => mem (a.eval regs mem)

/-- All source variables are below the scratch-register boundary. -/
def Bounded : Expr → Nat → Prop
  | .const _, _ => True
  | .var x, n => x < n
  | .bin _ a b, n => a.Bounded n ∧ b.Bounded n
  | .load a, n => a.Bounded n

instance instDecidableBounded : (e : Expr) → (n : Nat) → Decidable (e.Bounded n)
  | .const _, _ => isTrue trivial
  | .var x, n => inferInstanceAs (Decidable (x < n))
  | .bin _ a b, n =>
      @instDecidableAnd _ _ (instDecidableBounded a n) (instDecidableBounded b n)
  | .load a, n => instDecidableBounded a n

/-- A bound computed from syntax; callers do not need to annotate expressions. -/
def varBound : Expr → Nat
  | .const _ => 0
  | .var x => x + 1
  | .bin _ a b => max a.varBound b.varBound
  | .load a => a.varBound

theorem Bounded.mono {e : Expr} {n m : Nat} (h : e.Bounded n) (hnm : n ≤ m) :
    e.Bounded m := by
  induction e with
  | const => trivial
  | var x => exact Nat.lt_of_lt_of_le h hnm
  | bin op a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | load a ih => exact ih h

theorem bounded_varBound (e : Expr) : e.Bounded e.varBound := by
  induction e with
  | const => trivial
  | var => exact Nat.lt_succ_self _
  | bin op a b ia ib =>
      exact ⟨ia.mono (Nat.le_max_left _ _), ib.mono (Nat.le_max_right _ _)⟩
  | load a ih => exact ih

/-- Evaluation only depends on the source variables it reads and the heap. -/
theorem eval_congr {e : Expr} {n : Nat}
    {r₁ r₂ : Reg → Word w} {m₁ m₂ : Word w → Word w}
    (hb : e.Bounded n) (hr : ∀ x, x < n → r₁ x = r₂ x) (hm : m₁ = m₂) :
    e.eval r₁ m₁ = e.eval r₂ m₂ := by
  subst m₂
  induction e with
  | const => rfl
  | var x => exact hr x hb
  | bin op a b ia ib => simp only [eval, ia hb.1, ib hb.2]
  | load a ih => simp only [eval, ih hb]

/-- Array indexing is ordinary address arithmetic followed by one-word access.
The array representation layer is responsible for bounds and non-wrapping
addresses; this is not an uncosted host-array operation. -/
def index (base offset : Expr) : Expr := .load (.bin .add base offset)

@[simp] theorem eval_index (base offset : Expr) (regs : Reg → Word w)
    (mem : Word w → Word w) :
    (index base offset).eval regs mem =
      mem (base.eval regs mem + offset.eval regs mem) := rfl

end Expr
end Ram
