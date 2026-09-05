import Ram.Measured

/-!
# Total-correctness contracts with proved execution budgets

A contract supplies a terminating measured execution, its postcondition, and
an upper bound on that execution's compiler-derived machine count. The bound
is a proposition to prove sufficient, never an operation price or a source
annotation that changes the computation.

Loop rules combine invariant preservation with a decreasing natural variant.
The simpler potential rule uses the remaining budget itself as the variant:
each true iteration must pay for its guard, branch, body, and back-edge jump.
-/

namespace Ram.Source

/-- A total contract. Ghost input parameters can be captured by `P` and `Q`;
the budget may depend on the complete initial source state. -/
def Contract (n : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P Q : State w → Prop) (bound : State w → Nat) : Prop :=
  ∀ s, P s → ∃ steps t,
    MeasuredExec n program heapLimit depth stmt steps s t ∧ Q t ∧ steps ≤ bound s

namespace Contract

variable {w n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P P' Q Q' : State w → Prop} {bound bound' : State w → Nat}

/-- Strengthen the precondition, weaken the postcondition, or enlarge the
budget without changing the certified execution. -/
theorem consequence (h : Contract n program heapLimit depth stmt P Q bound)
    (pre : ∀ s, P' s → P s) (post : ∀ t, Q t → Q' t)
    (budget : ∀ s, P' s → bound s ≤ bound' s) :
    Contract n program heapLimit depth stmt P' Q' bound' := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s (pre s hs)
  exact ⟨steps, t, hx, post t hq, Nat.le_trans hb (budget s hs)⟩

theorem mono_post (h : Contract n program heapLimit depth stmt P Q bound)
    (post : ∀ t, Q t → Q' t) :
    Contract n program heapLimit depth stmt P Q' bound :=
  h.consequence (fun _ hp => hp) post (fun _ _ => Nat.le_refl _)

theorem mono_budget (h : Contract n program heapLimit depth stmt P Q bound)
    (budget : ∀ s, P s → bound s ≤ bound' s) :
    Contract n program heapLimit depth stmt P Q bound' :=
  h.consequence (fun _ hp => hp) (fun _ hq => hq) budget

/-- Call-depth capacity and execution-time budget are separate resources. -/
theorem mono_depth {depth' : Nat}
    (h : Contract n program heapLimit depth stmt P Q bound) (hd : depth ≤ depth') :
    Contract n program heapLimit depth' stmt P Q bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx.mono hd, hq, hb⟩

/-- Dropping the resource assertions leaves total source correctness. -/
theorem totalCorrect (h : Contract n program heapLimit depth stmt P Q bound) :
    TotalCorrect program stmt P (fun _ t => Q t) := by
  intro s hs
  obtain ⟨_, t, hx, hq, _⟩ := h s hs
  exact ⟨t, hx.erase.erase, hq⟩

/-- A source contract gives a checked executable's actual time bound, including
the prologue read and halt. The source postcondition is retained on its own
state; only the proved output and input observations are transferred directly. -/
theorem compile {code : Code} {input : List (Word w)}
    (h : Contract n program heapLimit depth stmt P Q bound)
    (hcompile : Compiler.compileChecked n program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal, Q sourceFinal ∧
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) targetFinal ∧
      targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  obtain ⟨steps, sourceFinal, hx, hq, hb⟩ := h (State.initial input) hp
  obtain ⟨targetFinal, ht, ho, hi⟩ := Compiler.compileChecked_terminatesWithin
    hcompile hcodefit hstackfit hx (Nat.add_le_add_right hb 2)
  exact ⟨sourceFinal, targetFinal, hq, ht, ho, hi⟩

theorem skip (P : State w → Prop) :
    Contract n program heapLimit depth .skip P P (fun _ => 0) := by
  intro s hs
  exact ⟨0, s, .skip, hs, Nat.le_refl _⟩

/-- Sequential budgets are evaluated at their actual respective entry states.
The compatibility premise relates the intermediate budget to the original one. -/
theorem seq {a b : Stmt} {R : State w → Prop}
    {firstBound secondBound : State w → Nat}
    (first : Contract n program heapLimit depth a P R firstBound)
    (second : Contract n program heapLimit depth b R Q secondBound)
    (compatible : ∀ s, P s → ∀ middle, R middle →
      firstBound s + secondBound middle ≤ bound s) :
    Contract n program heapLimit depth (.seq a b) P Q bound := by
  intro s hs
  obtain ⟨na, middle, ha, hm, hna⟩ := first s hs
  obtain ⟨nb, t, hb, hq, hnb⟩ := second middle hm
  refine ⟨na + nb, t, .seq ha hb, hq, ?_⟩
  exact Nat.le_trans (Nat.add_le_add hna hnb) (compatible s hs middle hm)

/-- A common sequence specialization with a state-independent second budget. -/
theorem seq_const {a b : Stmt} {R : State w → Prop} {secondBound : Nat}
    (first : Contract n program heapLimit depth a P R bound)
    (second : Contract n program heapLimit depth b R Q (fun _ => secondBound)) :
    Contract n program heapLimit depth (.seq a b) P Q (fun s => bound s + secondBound) :=
  first.seq second (fun _ _ _ _ => Nat.le_refl _)

/-- A loop contract proved by invariant preservation, a strictly decreasing
natural variant, and enough remaining budget for each executed iteration.
The guard length comes from generated code; the two extra steps are its
conditional branch and the actual back-edge jump. -/
theorem while_variant {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant budget : State w → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (exitBudget : ∀ s, invariant s → s.eval condition = 0 →
      (condition.compile (ABI.scratch n)).length + 1 ≤ budget s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      ∃ bodySteps t, MeasuredExec n program heapLimit depth body bodySteps s t ∧
        invariant t ∧ variant t < variant s ∧
        (condition.compile (ABI.scratch n)).length + 1 + bodySteps + 1 + budget t ≤ budget s) :
    Contract n program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0) budget := by
  have loop : ∀ k s, variant s = k → invariant s →
      ∃ steps t, MeasuredExec n program heapLimit depth (.while condition body) steps s t ∧
        (invariant t ∧ t.eval condition = 0) ∧ steps ≤ budget s := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro s hvariant hinv
        by_cases hz : s.eval condition = 0
        · exact ⟨_, s, .whileFalse (reads s hinv) hz, ⟨hinv, hz⟩,
            exitBudget s hinv hz⟩
        · obtain ⟨bodySteps, middle, hbody, hmid, hdecrease, hbudget⟩ := iteration s hinv hz
          have hlt : variant middle < k := by omega
          obtain ⟨restSteps, t, hrest, hpost, hrestBudget⟩ :=
            ih (variant middle) hlt middle rfl hmid
          refine ⟨_, t, .whileTrue (reads s hinv) hz hbody hrest, hpost, ?_⟩
          omega
  intro s hs
  exact loop (variant s) s rfl hs

/-- The remaining natural budget already decreases strictly, because a true
iteration executes at least the branch and back-edge transitions. Users need
not provide a second, redundant termination measure. -/
theorem while_potential {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (budget : State w → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (exitBudget : ∀ s, invariant s → s.eval condition = 0 →
      (condition.compile (ABI.scratch n)).length + 1 ≤ budget s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      ∃ bodySteps t, MeasuredExec n program heapLimit depth body bodySteps s t ∧
        invariant t ∧
        (condition.compile (ABI.scratch n)).length + 1 + bodySteps + 1 + budget t ≤ budget s) :
    Contract n program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0) budget := by
  apply while_variant invariant budget budget reads exitBudget
  intro s hs hz
  obtain ⟨bodySteps, t, hb, hi, hc⟩ := iteration s hs hz
  exact ⟨bodySteps, t, hb, hi, by omega, hc⟩

/-- Use a separately proved body contract in the potential rule. The ghost
entry state allows its postcondition to relate old and new potential. -/
theorem while_contract {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (budget bodyBound : State w → Nat)
    (reads : ∀ s, invariant s → condition.ReadsBelow heapLimit s.regs s.mem)
    (exitBudget : ∀ s, invariant s → s.eval condition = 0 →
      (condition.compile (ABI.scratch n)).length + 1 ≤ budget s)
    (iteration : ∀ s, invariant s → s.eval condition ≠ 0 →
      Contract n program heapLimit depth body (fun initial => initial = s)
        (fun t => invariant t ∧
          (condition.compile (ABI.scratch n)).length + 1 + bodyBound s + 1 + budget t ≤ budget s)
        (fun _ => bodyBound s)) :
    Contract n program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0) budget := by
  apply while_potential invariant budget reads exitBudget
  intro s hs hz
  obtain ⟨bodySteps, t, hb, ⟨hi, hc⟩, hbound⟩ := iteration s hs hz s rfl
  change bodySteps ≤ bodyBound s at hbound
  exact ⟨bodySteps, t, hb, hi, by omega⟩

end Contract
end Ram.Source
