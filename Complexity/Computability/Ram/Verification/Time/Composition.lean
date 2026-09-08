/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.Basic
import Complexity.Data.Nat.Log

/-!
# Compositional time bounds without fuel

Primitive bounds use the generated instruction lengths. Calls use a callee's
time bound, while loops combine a separately proved functional body relation
with a mathematical recurrence inequality. None of these rules changes the
execution semantics or requires choosing and threading unused fuel.

These are conditional bounds on completed executions. Safety and termination
are supplied separately by total correctness, not inferred from `TimeBound`.
-/

namespace Ram.Source.TimeBound

variable {control heapLimit depth : Nat} {program : Program}
variable {P : State w → Prop}

/-- Skipping executes no instructions. -/
theorem skip (P : State w → Prop) :
    TimeBound control program heapLimit depth .skip P (fun _ => 0) := by
  intro s _ steps t hx
  cases hx
  exact Nat.le_refl _

/-- Assignment is bounded by its generated expression and move block. -/
theorem assign {dst : Reg} {value : Expr} :
    TimeBound control program heapLimit depth (.assign dst value) P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.assign dst value)) := by
  intro s _ steps t hx
  cases hx
  exact Nat.le_refl _

/-- Reassociation preserves both the executed sequence and its total count. -/
theorem seq_assoc_iff {a b c : Stmt} {bound : State w → Nat} :
    TimeBound control program heapLimit depth (.seq (.seq a b) c) P bound ↔
      TimeBound control program heapLimit depth (.seq a (.seq b c)) P bound := by
  constructor
  · intro h s hs steps t execution
    cases execution with
    | seq first rest =>
      cases rest with
      | seq second third =>
        simpa only [Nat.add_assoc] using
          h s hs _ t (.seq (.seq first second) third)
  · intro h s hs steps t execution
    cases execution with
    | seq first third =>
      cases first with
      | seq first second =>
        simpa only [Nat.add_assoc] using
          h s hs _ t (.seq first (.seq second third))

/-- A leading skip changes neither the entry state nor the remaining count. -/
theorem skip_seq_iff {tail : Stmt} {bound : State w → Nat} :
    TimeBound control program heapLimit depth (.seq .skip tail) P bound ↔
      TimeBound control program heapLimit depth tail P bound := by
  constructor
  · intro h s hs steps t execution
    simpa only [Nat.zero_add] using h s hs _ t (.seq .skip execution)
  · intro h s hs steps t execution
    cases execution with
    | seq first second =>
      cases first
      simpa only [Nat.zero_add] using h s hs _ t second

/-- Advance an assignment at one actual entry state, charging its generated
expression and move block before bounding the tail. The subtraction only
describes a separate time-proof obligation; it does not supply execution fuel.
Read safety comes from each completed execution, not from this conditional bound. -/
theorem assign_seq_at {dst : Reg} {value : Expr} {tail : Stmt}
    {entry : State w} {overall : Nat}
    (budget : LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
      (.assign dst value) ≤ overall)
    (continuation : TimeBound control program heapLimit depth tail
      (fun s => s = entry.setReg dst (entry.eval value))
      (fun _ => overall -
        LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (.assign dst value))) :
    TimeBound control program heapLimit depth (.seq (.assign dst value) tail)
      (fun s => s = entry) (fun _ => overall) := by
  rintro s rfl steps finish execution
  cases execution with
  | seq first second =>
    cases first
    have remaining := continuation _ rfl _ _ second
    dsimp only at remaining ⊢
    omega

/-- Store accounting includes evaluation of its address and value. -/
theorem store {address value : Expr} :
    TimeBound control program heapLimit depth (.store address value) P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.store address value)) := by
  intro s _ steps t hx
  cases hx
  exact Nat.le_refl _

/-- Every completed read executes its generated input block. -/
theorem read {dst : Reg} :
    TimeBound control program heapLimit depth (.read dst) P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.read dst)) := by
  intro s _ steps t hx
  cases hx
  exact Nat.le_refl _

/-- Write accounting includes evaluation of the value being output. -/
theorem write {value : Expr} :
    TimeBound control program heapLimit depth (.write value) P
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.write value)) := by
  intro s _ steps t hx
  cases hx
  exact Nat.le_refl _

/-- Reuse a callee's time bound at its actual argument state. The overhead
comes from the same callee-sized save/restore blocks as measured execution.
Calling-convention safety need not be reproved for this conditional bound. -/
theorem call {fn : Nat} {dsts : List Reg} {args : List Expr} {f : Func}
    {calleePre : State w → Prop} {bodyBound : State w → Nat}
    (lookup : program[fn]? = some f)
    (pre : ∀ s, P s → calleePre (s.enter (args.map s.eval)))
    (cost : TimeBound control program heapLimit depth f.body calleePre bodyBound) :
    TimeBound control program heapLimit (depth + 1) (.call dsts fn args) P
      (fun s => (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bodyBound (s.enter (args.map s.eval)) +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length) := by
  intro s hs steps t hx
  cases hx with
  | call found _ _ _ _ hb _ =>
    have hf : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have hbody := cost _ (pre s hs) _ _ hb
    dsimp only
    omega

/-- A recurrence for the remaining time of a loop. The body specification
contains its ordinary functional relation `R`; the separate `progress` proof
turns that relation into invariant preservation and a budget decrease.

The final false guard and every true guard/back-edge are included. The proof
follows an actual completed loop execution, so this rule does not assume or
claim termination of the loop. -/
theorem while_potential {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (bound bodyBound : State w → Nat)
    {R : State w → State w → Prop}
    (functional : TotalRelContract program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0) R)
    (cost : TimeBound control program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0) bodyBound)
    (exitBudget : ∀ s, invariant s → s.eval condition = 0 →
      (condition.compile (ABI.scratch control)).length + 1 ≤ bound s)
    (progress : ∀ s t, invariant s → s.eval condition ≠ 0 → R s t →
      invariant t ∧
        (condition.compile (ABI.scratch control)).length + 1 + bodyBound s + 1 +
          bound t ≤ bound s) :
    TimeBound control program heapLimit depth (.while condition body) invariant bound := by
  have loop : ∀ steps s, invariant s → ∀ t,
      LocalMeasuredExec control program heapLimit depth (.while condition body) steps s t →
        steps ≤ bound s := by
    intro steps
    induction steps using Nat.strongRecOn with
    | ind steps ih =>
      intro s hs t hx
      cases hx with
      | whileFalse _ hz => exact exitBudget s hs hz
      | whileTrue _ hz hb hr =>
        obtain ⟨middle, hm, hrelation⟩ := functional s ⟨hs, hz⟩
        have same := hm.deterministic hb.erase
        have hprogress := progress s middle hs hz hrelation
        rw [same] at hprogress
        have hbody := cost s ⟨hs, hz⟩ _ _ hb
        have hrest := ih _ (by omega) _ hprogress.1 _ hr
        omega
  intro s hs steps t hx
  exact loop steps s hs t hx

/-- A decreasing natural variant bounds the number of completed iterations.
The body relation is the same budget-free invariant/progress fact used for
termination; the instruction bound is supplied separately. Guard evaluation,
the back-edge and the final false guard are all charged by the compiler. -/
theorem while_linear {condition : Expr} {body : Stmt}
    (invariant : State w → Prop) (variant : State w → Nat) (bodyBudget : Nat)
    (functional : TotalRelContract program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0)
      (fun s t => invariant t ∧ variant t < variant s))
    (cost : TimeBound control program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0) (fun _ => bodyBudget)) :
    TimeBound control program heapLimit depth (.while condition body) invariant
      (fun s => variant s *
        ((condition.compile (ABI.scratch control)).length + 1 + bodyBudget + 1) +
        ((condition.compile (ABI.scratch control)).length + 1)) := by
  apply while_potential invariant _ _ functional cost
  · intro s _ _
    omega
  · intro s t _ _ ht
    refine ⟨ht.1, ?_⟩
    have hmul := Nat.mul_le_mul_right
      ((condition.compile (ABI.scratch control)).length + 1 + bodyBudget + 1)
      (Nat.succ_le_of_lt ht.2)
    rw [Nat.succ_mul] at hmul
    omega

/-- Dividing a positive natural measure gives a logarithmic bound on completed
iterations. The functional relation and the body instruction bound are supplied
separately. The condition, back-edge and final false guard retain their actual
compiler-derived costs; this conditional rule does not assert loop termination. -/
theorem while_div {condition : Expr} {body : Stmt} (base : Nat) (hb : 1 < base)
    (invariant : State w → Prop) (measure : State w → Nat) (bodyBudget : Nat)
    (positive : ∀ s, invariant s → s.eval condition ≠ 0 → 0 < measure s)
    (functional : TotalRelContract program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0)
      (fun s t => invariant t ∧ measure t ≤ measure s / base))
    (cost : TimeBound control program heapLimit depth body
      (fun s => invariant s ∧ s.eval condition ≠ 0) (fun _ => bodyBudget)) :
    TimeBound control program heapLimit depth (.while condition body) invariant
      (fun s => Nat.clog base (measure s + 1) *
        ((condition.compile (ABI.scratch control)).length + 1 + bodyBudget + 1) +
        ((condition.compile (ABI.scratch control)).length + 1)) := by
  refine while_linear invariant (fun s => Nat.clog base (measure s + 1)) bodyBudget
    (functional.consequence (fun _ hs => hs) ?_) cost
  intro s t hs ht
  exact ⟨ht.1, lt_of_le_of_lt
    (Nat.clog_mono_right base (Nat.add_le_add_right ht.2 1))
    (Nat.clog_div_succ_lt hb (positive s hs.1 hs.2))⟩

end Ram.Source.TimeBound
