import Ram.Execution

/-!
# Uniform runtime bounds for a fixed RAM program

The code is fixed outside the quantifiers over inputs and word widths. Both
exact upper bounds and asymptotic bounds require successful termination and the
postcondition, not merely an implication about an execution that might not
exist. Encoding, admissible widths, and the input-size function belong to the
problem specification; changing them changes the claim.

The asymptotic convention is the usual eventual constant-factor upper bound
on natural-valued functions. These definitions use the same `TerminatesWithin`
machine judgment as the compiler theorems; they introduce no operation prices.
-/

namespace Ram

/-- Successful termination and the functional postcondition for every legal
input, including inputs below an asymptotic threshold. -/
def UniformCorrect {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (post : ∀ w, Input → State w → Prop) : Prop :=
  ∀ w input, admissible w input →
    ∃ steps finish, Exec code steps (State.initial (encode w input)) finish ∧
      finish.status = .halted ∧ post w input finish

/-- A total functional specification and time bound, uniform in the word width
and input, for one fixed instruction list. Input encoding costs inside the
program are counted; anything done by `encode` is part of the external problem
encoding and must be specified as such. -/
def UniformTimeBound {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (bound : Nat → Nat) : Prop :=
  ∀ w input, admissible w input →
    ∃ finish, TerminatesWithin code (bound (size input))
      (State.initial (encode w input)) finish ∧ post w input finish

/-- Total correctness on all legal inputs, and eventual constant-factor time,
for a single fixed code list. Neither the threshold nor the constant depends on
the particular input or word width. Small inputs cannot hide a correctness or
termination failure below the asymptotic threshold. -/
def UniformBigO {Input : Type} (code : Code)
    (encode : ∀ w, Input → List (Word w)) (admissible : Nat → Input → Prop)
    (size : Input → Nat) (post : ∀ w, Input → State w → Prop)
    (growth : Nat → Nat) : Prop :=
  UniformCorrect code encode admissible post ∧
  ∃ constant threshold, 0 < constant ∧
    ∀ w input, admissible w input → threshold ≤ size input →
      ∃ finish, TerminatesWithin code (constant * growth (size input))
        (State.initial (encode w input)) finish ∧ post w input finish

theorem UniformTimeBound.correct {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {bound : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post bound) :
    UniformCorrect code encode admissible post := by
  intro w input hadmissible
  obtain ⟨finish, ⟨steps, _, he, hhalt⟩, hp⟩ := h w input hadmissible
  exact ⟨steps, finish, he, hhalt, hp⟩

theorem UniformTimeBound.mono {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {a b : Nat → Nat}
    (h : UniformTimeBound code encode admissible size post a)
    (hab : ∀ n, a n ≤ b n) : UniformTimeBound code encode admissible size post b := by
  intro w input hadmissible
  obtain ⟨finish, he, hp⟩ := h w input hadmissible
  exact ⟨finish, he.mono (hab (size input)), hp⟩

/-- Transfer a proved concrete machine bound to an eventual asymptotic bound. -/
theorem UniformTimeBound.bigO {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop}
    {bound growth : Nat → Nat} {constant threshold : Nat}
    (h : UniformTimeBound code encode admissible size post bound)
    (hc : 0 < constant)
    (hbound : ∀ n, threshold ≤ n → bound n ≤ constant * growth n) :
    UniformBigO code encode admissible size post growth := by
  refine ⟨h.correct, constant, threshold, hc, ?_⟩
  intro w input hadmissible hsize
  obtain ⟨finish, he, hp⟩ := h w input hadmissible
  exact ⟨finish, he.mono (hbound (size input) hsize), hp⟩

/-- A concrete affine machine bound yields linear asymptotic time, including
the fixed setup/termination overhead rather than silently dropping it. -/
theorem UniformTimeBound.linear {Input : Type} {code : Code}
    {encode : ∀ w, Input → List (Word w)} {admissible : Nat → Input → Prop}
    {size : Input → Nat} {post : ∀ w, Input → State w → Prop} {a b : Nat}
    (h : UniformTimeBound code encode admissible size post (fun n => a * n + b)) :
    UniformBigO code encode admissible size post (fun n => n) := by
  apply h.bigO (constant := a + b + 1) (threshold := 1) (Nat.zero_lt_succ _)
  intro n hn
  have hb : b ≤ b * n := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left b hn
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end Ram
