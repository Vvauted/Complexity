/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Program.Basic

/-!
# Total-correctness contracts with proved execution budgets

A contract supplies a terminating measured execution, its postcondition, and
an upper bound on that execution's compiler-derived machine count. The bound
is a proposition to prove sufficient, never an operation price or a source
annotation that changes the computation.

The default contracts use the callee-local compiler: `n` locates reserved
registers, while each function's declared local bound determines its actual
save/restore work. Compilation produces that same optimized instruction stream.

Loop rules combine invariant preservation with a decreasing natural variant.
The simpler potential rule uses the remaining budget itself as the variant:
each true iteration must pay for its guard, branch, body, and back-edge jump.
-/

namespace Ram.Source

namespace State

@[simp] theorem eval_const (s : State w) (value : Nat) :
    s.eval (.const value) = BitVec.ofNat w value := rfl

@[simp] theorem eval_var (s : State w) (r : Reg) : s.eval (.var r) = s.regs r := rfl

@[simp] theorem eval_bin (s : State w) (op : BinOp) (a b : Expr) :
    s.eval (.bin op a b) = op.eval (s.eval a) (s.eval b) := rfl

@[simp] theorem eval_load (s : State w) (address : Expr) :
    s.eval (.load address) = s.mem (s.eval address) := rfl

@[simp] theorem setReg_mem (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).mem = s.mem := rfl

@[simp] theorem setReg_input (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).input = s.input := rfl

@[simp] theorem setReg_outputRev (s : State w) (dst : Reg) (value : Word w) :
    (s.setReg dst value).outputRev = s.outputRev := rfl

@[simp] theorem setMem_regs (s : State w) (address value : Word w) :
    (s.setMem address value).regs = s.regs := rfl

@[simp] theorem setMem_input (s : State w) (address value : Word w) :
    (s.setMem address value).input = s.input := rfl

@[simp] theorem setMem_outputRev (s : State w) (address value : Word w) :
    (s.setMem address value).outputRev = s.outputRev := rfl

end State

/-- A total contract. Ghost input parameters can be captured by `P` and `Q`;
the budget may depend on the complete initial source state. -/
def Contract (n : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P Q : State w → Prop) (bound : State w → Nat) : Prop :=
  ∀ s, P s → ∃ steps t,
    LocalMeasuredExec n program heapLimit depth stmt steps s t ∧ Q t ∧ steps ≤ bound s

/-- A total contract whose postcondition keeps the actual entry state. This
relation lets later budgets and assertions refer to the original input without
requiring a uniform bound over unrelated intermediate states. -/
def RelContract (n : Nat) (program : Program) (heapLimit depth : Nat) (stmt : Stmt)
    (P : State w → Prop) (Q : State w → State w → Prop) (bound : State w → Nat) : Prop :=
  ∀ s, P s → ∃ steps t,
    LocalMeasuredExec n program heapLimit depth stmt steps s t ∧ Q s t ∧ steps ≤ bound s

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
    (hcompile : LocalCompiler.compileChecked n program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal, Q sourceFinal ∧
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) targetFinal ∧
      targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  obtain ⟨steps, sourceFinal, hx, hq, hb⟩ := h (State.initial input) hp
  obtain ⟨targetFinal, ht, ho, hi⟩ := LocalCompiler.compileChecked_terminatesWithin
    hcompile hcodefit hstackfit hx (Nat.add_le_add_right hb 2)
  exact ⟨sourceFinal, targetFinal, hq, ht, ho, hi⟩

/-- A checked contract with heap observations as well as I/O. Any source
postcondition about addresses below `heapLimit` can be transported to the
halted target heap using the returned agreement; stack words remain private. -/
theorem compile_heap {code : Code} {input : List (Word w)}
    (h : Contract n program heapLimit depth stmt P Q bound)
    (hcompile : LocalCompiler.compileChecked n program stmt = some code)
    (hcodefit : code.length < 2 ^ w)
    (hstackfit : heapLimit + depth * ABI.frameSize n < 2 ^ w)
    (hp : P (State.initial input)) :
    ∃ sourceFinal targetFinal, Q sourceFinal ∧
      Ram.TerminatesWithin code (bound (State.initial input) + 2)
        (Ram.State.initial (BitVec.ofNat w heapLimit :: input)) targetFinal ∧
      HeapEqBelow heapLimit sourceFinal.mem targetFinal.mem ∧
      targetFinal.output = sourceFinal.output ∧ targetFinal.input = sourceFinal.input := by
  obtain ⟨steps, sourceFinal, hx, hq, hb⟩ := h (State.initial input) hp
  obtain ⟨targetFinal, ht, hm, ho, hi⟩ := LocalCompiler.compileChecked_terminatesWithin_heap
    hcompile hcodefit hstackfit hx (Nat.add_le_add_right hb 2)
  exact ⟨sourceFinal, targetFinal, hq, ht, hm, ho, hi⟩

theorem skip (P : State w → Prop) :
    Contract n program heapLimit depth .skip P P (fun _ => 0) := by
  intro s hs
  exact ⟨0, s, .skip, hs, Nat.le_refl _⟩

/-- Introduce a ghost name for the actual entry state. It is available in the
postcondition and budget proof, but is never part of the executed program. -/
theorem with_entry
    (h : ∀ entry, P entry → Contract n program heapLimit depth stmt
      (fun s => s = entry) Q (fun _ => bound entry)) :
    Contract n program heapLimit depth stmt P Q bound := by
  intro s hs
  exact h s hs s rfl

/-- Assignment is proved by substituting its actual state update. Its budget
is the length of the generated expression and register-move block. -/
theorem assign {dst : Reg} {value : Expr}
    (reads : ∀ s, P s → value.ReadsBelow heapLimit s.regs s.mem)
    (post : ∀ s, P s → Q (s.setReg dst (s.eval value))) :
    Contract n program heapLimit depth (.assign dst value) P Q
      (fun _ => LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program)
        (.assign dst value)) := by
  intro s hs
  exact ⟨_, _, .assign (reads s hs), post s hs, Nat.le_refl _⟩

/-- One source store evaluates its two pure expressions and writes one word.
The destination and every nested load must lie inside the source heap. -/
theorem store {address value : Expr}
    (addressReads : ∀ s, P s → address.ReadsBelow heapLimit s.regs s.mem)
    (valueReads : ∀ s, P s → value.ReadsBelow heapLimit s.regs s.mem)
    (destination : ∀ s, P s → (s.eval address).toNat < heapLimit)
    (post : ∀ s, P s → Q (s.setMem (s.eval address) (s.eval value))) :
    Contract n program heapLimit depth (.store address value) P Q
      (fun _ => LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program)
        (.store address value)) := by
  intro s hs
  exact ⟨_, _, .store (addressReads s hs) (valueReads s hs) (destination s hs),
    post s hs, Nat.le_refl _⟩

/-- A read contract must establish the existence of its next input word. -/
theorem read {dst : Reg}
    (available : ∀ s, P s → ∃ value rest,
      s.input = value :: rest ∧ Q { s.setReg dst value with input := rest }) :
    Contract n program heapLimit depth (.read dst) P Q (fun _ => 1) := by
  intro s hs
  obtain ⟨value, rest, hi, hq⟩ := available s hs
  exact ⟨1, _, .read hi, hq, Nat.le_refl _⟩

theorem write {value : Expr}
    (reads : ∀ s, P s → value.ReadsBelow heapLimit s.regs s.mem)
    (post : ∀ s, P s → Q { s with outputRev := s.eval value :: s.outputRev }) :
    Contract n program heapLimit depth (.write value) P Q
      (fun _ => LocalCompiler.stmtSize n (LocalCompiler.calleeLocals program)
        (.write value)) := by
  intro s hs
  exact ⟨_, _, .write (reads s hs), post s hs, Nat.le_refl _⟩

/-- Each branch receives its guard fact. The true branch also executes the
compiler's skip-over-else jump; all these counts are actual machine steps. -/
theorem ite {condition : Expr} {yes no : Stmt} {yesBound noBound : State w → Nat}
    (reads : ∀ s, P s → condition.ReadsBelow heapLimit s.regs s.mem)
    (ifTrue : Contract n program heapLimit depth yes
      (fun s => P s ∧ s.eval condition ≠ 0) Q yesBound)
    (ifFalse : Contract n program heapLimit depth no
      (fun s => P s ∧ s.eval condition = 0) Q noBound) :
    Contract n program heapLimit depth (.ite condition yes no) P Q
      (fun s => (condition.compile (ABI.scratch n)).length + 1 +
        if s.eval condition = 0 then noBound s else yesBound s + 1) := by
  intro s hs
  by_cases hz : s.eval condition = 0
  · obtain ⟨steps, t, hx, hq, hb⟩ := ifFalse s ⟨hs, hz⟩
    refine ⟨_, t, .iteFalse (reads s hs) hz hx, hq, ?_⟩
    simpa only [if_pos hz] using Nat.add_le_add_left hb
      ((condition.compile (ABI.scratch n)).length + 1)
  · obtain ⟨steps, t, hx, hq, hb⟩ := ifTrue s ⟨hs, hz⟩
    refine ⟨_, t, .iteTrue (reads s hs) hz hx, hq, ?_⟩
    simp only [if_neg hz]
    omega

/-- Reuse a callee contract at a fresh local frame, then evaluate its return
expressions there and restore the caller. The budget includes argument setup,
the entry jump, the body, the concrete return code, and every receive instruction.
Save/restore work is determined by `f.locals`, not the global register bound. -/
theorem call {fn : Nat} {dsts : List Reg} {args : List Expr} {f : Func}
    {bodyBound : State w → Nat}
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (resultCount : dsts.length = f.results.length)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ s, P s → ∀ arg ∈ args, arg.ReadsBelow heapLimit s.regs s.mem)
    (callee : ∀ caller, P caller →
      Contract n program heapLimit depth f.body
        (fun s => s = caller.enter (args.map caller.eval))
        (fun finish => (∀ result ∈ f.results,
          result.ReadsBelow heapLimit finish.regs finish.mem) ∧
          Q (caller.leave finish dsts f.results)) (fun _ => bodyBound caller)) :
    Contract n program heapLimit (depth + 1) (.call dsts fn args) P Q
      (fun caller => (ABI.callPrefixLocals n f.locals args 0).length + 1 + bodyBound caller +
        (ABI.returnCodeResultsLocals n f.locals f.results).length + dsts.length) := by
  intro s hs
  obtain ⟨bodySteps, finish, hx, ⟨hr, hq⟩, hb⟩ :=
    callee s hs (s.enter (args.map s.eval)) rfl
  change bodySteps ≤ bodyBound s at hb
  refine ⟨_, _, .call lookup arity resultCount frame (arguments s hs) hx hr, hq, ?_⟩
  exact Nat.add_le_add_right
    (Nat.add_le_add_right
      (Nat.add_le_add_left hb ((ABI.callPrefixLocals n f.locals args 0).length + 1))
      (ABI.returnCodeResultsLocals n f.locals f.results).length) dsts.length

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
      ∃ bodySteps t, LocalMeasuredExec n program heapLimit depth body bodySteps s t ∧
        invariant t ∧ variant t < variant s ∧
        (condition.compile (ABI.scratch n)).length + 1 + bodySteps + 1 + budget t ≤ budget s) :
    Contract n program heapLimit depth (.while condition body) invariant
      (fun t => invariant t ∧ t.eval condition = 0) budget := by
  have loop : ∀ k s, variant s = k → invariant s →
      ∃ steps t, LocalMeasuredExec n program heapLimit depth (.while condition body) steps s t ∧
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
      ∃ bodySteps t, LocalMeasuredExec n program heapLimit depth body bodySteps s t ∧
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

namespace RelContract

variable {w n heapLimit depth : Nat} {program : Program} {stmt : Stmt}
variable {P : State w → Prop} {Q R : State w → State w → Prop}
variable {bound : State w → Nat}

/-- A relational postcondition is equivalently a family of ordinary contracts
with the entry state captured as a ghost parameter. -/
theorem iff_entry :
    RelContract n program heapLimit depth stmt P Q bound ↔
      ∀ entry, P entry → Contract n program heapLimit depth stmt
        (fun s => s = entry) (Q entry) (fun _ => bound entry) := by
  constructor
  · intro h entry hp s hs
    subst s
    exact h entry hp
  · intro h entry hp
    exact h entry hp entry rfl

theorem toContract {post : State w → Prop}
    (h : RelContract n program heapLimit depth stmt P Q bound)
    (weaken : ∀ entry finish, P entry → Q entry finish → post finish) :
    Contract n program heapLimit depth stmt P post bound := by
  intro s hs
  obtain ⟨steps, t, hx, hq, hb⟩ := h s hs
  exact ⟨steps, t, hx, weaken s t hs hq, hb⟩

/-- The second contract and its budget retain the original entry state.
Only intermediate states related to that same entry are quantified. -/
theorem seq {a b : Stmt} {firstBound : State w → Nat}
    {secondBound : State w → State w → Nat}
    (first : RelContract n program heapLimit depth a P R firstBound)
    (second : ∀ entry, P entry →
      Contract n program heapLimit depth b (R entry) (Q entry) (secondBound entry))
    (compatible : ∀ entry middle, P entry → R entry middle →
      firstBound entry + secondBound entry middle ≤ bound entry) :
    RelContract n program heapLimit depth (.seq a b) P Q bound := by
  intro s hs
  obtain ⟨na, middle, ha, hm, hna⟩ := first s hs
  obtain ⟨nb, t, hb, hq, hnb⟩ := second s hs middle hm
  exact ⟨na + nb, t, .seq ha hb, hq,
    Nat.le_trans (Nat.add_le_add hna hnb) (compatible s middle hs hm)⟩

end RelContract
end Ram.Source
