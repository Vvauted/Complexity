/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn
import Complexity.Computability.Ram.Array.Fold.Call
import Complexity.Computability.Ram.Verification.Time.Composition
import Complexity.Computability.Ram.Verification.Time.Function

/-!
# Array iteration with a verified scalar function call

Each iteration loads an array element and passes that word and the accumulator
to a fixed source function. Its budget-free contract establishes the mathematical
step and preservation of shared state. The array-iteration rule supplies cursor
progress, termination and framing; no Lean callback is executed for free.

The separate exact-count theorem accepts a proved constant callee-body count.
The existing call compiler adds argument evaluation, frame handling and return
instructions, while the iteration rule counts initialization, loads and guards.

The conditional time-bound rules instead accept a helper's function-level upper
bound. They measure only completed traversals and require no helper totality or
exact count for arbitrary body-entry states.
-/

namespace Ram.Source.Array.ForIn.Call

/-- The actual two-argument call after the iteration has loaded its element. -/
def body (registers : Registers) (fn : Nat) : Stmt :=
  .call [registers.accumulator] fn [.var registers.accumulator, .var registers.element]

/-- A verified source function implements one accumulator update on the loaded
word. Its returned value is assigned by the actual call instruction. -/
theorem body_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {step : Word w → Word w → Word w}
    (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (s : State w) :
    SafeExec program heapLimit (depth + 1) (body registers fn) s
      (s.setReg registers.accumulator
        (step (s.regs registers.accumulator) (s.regs registers.element))) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    contract (s.regs registers.accumulator) (s.regs registers.element)
      [s.regs registers.accumulator, s.regs registers.element] s rfl
  have resultCount : [registers.accumulator].length = f.results.length := by
    simpa only [List.length_cons, List.length_nil] using execution.length_eq
  exact execution.call (dsts := [registers.accumulator])
    (exprs := [.var registers.accumulator, .var registers.element]) lookup resultCount
    (by simp [Expr.ReadsBelow])

/-- Read a represented array through one fixed, verified function call per
element. The input expressions are evaluated in source order, and the frame
excludes the accumulator, element binding and both private cursor locals. -/
theorem forIn_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {base length : Expr} {step : Word w → Word w → Word w}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (s : State w) (xs : List (Word w))
    (baseReads : base.ReadsBelow heapLimit s.regs s.mem)
    (lengthReads : length.ReadsBelow heapLimit
      (s.setReg registers.pointer (s.eval base)).regs s.mem)
    (represented : ArrayRep s.mem (s.eval base) xs)
    (count : ((s.setReg registers.pointer (s.eval base)).eval length).toNat = xs.length)
    (heap : (s.eval base).toNat + xs.length ≤ heapLimit)
    (fit : (s.eval base).toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit (depth + 1)
        (Stmt.forIn registers.pointer registers.remaining registers.element base length
          (body registers fn)) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → r ≠ registers.element → t.regs r = s.regs r := by
  obtain ⟨t, execution, result, _, _, _, memory, input, output, other⟩ :=
    ForIn.forIn_safe registers (R := fun _ => True) hw
      (fun current _ => by
        simpa only [State.setReg, if_neg (Ne.symm registers.element_ne_accumulator),
          if_pos rfl] using
          body_safe registers lookup contract
            (current.setReg registers.element (current.mem (current.regs registers.pointer))))
      (by intros; trivial) s xs trivial baseReads lengthReads represented count heap fit
  exact ⟨t, execution, result, memory, input, output, other⟩

/-- The call restores its caller locals before assigning the accumulator, so
the private remaining-count local is unchanged even without a functional spec. -/
theorem body_remaining (registers : Registers) {program : Program}
    {fn heapLimit depth : Nat} {s t : State w}
    (h : SafeExec program heapLimit depth (body registers fn) s t) :
    t.regs registers.remaining = s.regs registers.remaining := by
  cases h with
  | call _ _ _ _ _ _ _ =>
    simp [State.leave, registers.remaining_ne_accumulator]

/-- A proved constant callee-body count determines this call's exact cost,
including both scalar arguments, the callee-sized frame and its return code. -/
theorem body_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat}
    (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1) (body registers fn) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1) (body registers fn)
      (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
        bodySteps) s t := by
  obtain ⟨steps, measured⟩ := h.exists_localMeasured control
  cases measured with
  | call found arity resultCount frame arguments callee results =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have count := cost callee
    have call := LocalMeasuredExec.call (dsts := [registers.accumulator])
      found arity resultCount frame arguments callee results
    rw [count] at call
    exact call

/-- Count the same completed iteration, including cursor initialization, every
element load, both cursor updates and the loop's guards and backedges. The cost
premise concerns the actual callee body, independently of functional correctness. -/
theorem forIn_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat} {base length : Expr}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn)) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn))
      ((base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
          bodySteps + 14) *
          ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4) s t :=
  ForIn.forIn_localMeasured registers hw (body_remaining registers)
    (body_localMeasured registers lookup cost) h

/-- Bound one actual loaded-element iteration using the helper's conditional
function bound. The load and the two cursor assignments retain their real costs. -/
private theorem iteration_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat}
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1)
      (Stmt.forInBody registers.pointer registers.remaining registers.element (body registers fn))
      (fun _ => True)
      (fun _ => Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget + 11) := by
  have callBound : TimeBound (w := w) control program heapLimit (depth + 1) (body registers fn)
      (fun _ => True) (fun _ => Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget) := by
    simpa only [body, Fold.Call.callSteps, List.length_cons, List.length_nil] using
      time.call (dsts := [registers.accumulator])
        (args := [.var registers.accumulator, .var registers.element])
        (R := fun _ => True) lookup (fun _ _ => by simp)
  intro s _ steps t execution
  cases execution with
  | seq loaded rest =>
    cases loaded with
    | assign _ =>
      cases rest with
      | seq called advance =>
        have callCount := callBound _ trivial _ _ called
        have advanceCount := (advance.deterministic
          (Fold.advanceCursor_localMeasured registers.toRegisters advance.erase)).1
        change 3 + (_ + _) ≤ Fold.Call.callSteps control f
          [.var registers.accumulator, .var registers.element] bodyBudget + 11
        dsimp only at callCount
        omega

/-- Bound every completed iteration loop without assuming that its helper
terminates on other inputs. The existing linear-loop rule is applied only to
states with a completed suffix, witnessed by the very execution being bounded. -/
theorem loop_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat} (hw : 0 < w)
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1)
      (Stmt.forInLoop registers.pointer registers.remaining registers.element (body registers fn))
      (fun _ => True)
      (fun s => (Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget + 14) *
          (s.regs registers.remaining).toNat + 2) := by
  let iteration :=
    Stmt.forInBody registers.pointer registers.remaining registers.element (body registers fn)
  let completed := fun s : State w => ∃ finish,
    SafeExec program heapLimit (depth + 1) (.while (.var registers.remaining) iteration) s finish
  have functional : TotalRelContract program heapLimit (depth + 1) iteration
      (fun s => completed s ∧ s.eval (.var registers.remaining) ≠ 0)
      (fun s t => completed t ∧
        (t.regs registers.remaining).toNat < (s.regs registers.remaining).toNat) := by
    rintro s ⟨⟨finish, execution⟩, nonzero⟩
    cases execution with
    | whileFalse _ zero => exact False.elim (nonzero zero)
    | whileTrue _ _ first rest =>
      refine ⟨_, first, ⟨_, rest⟩, ?_⟩
      have decrease := ForIn.body_remaining registers (body_remaining registers) first
      change s.regs registers.remaining ≠ 0 at nonzero
      have positive : 0 < (s.regs registers.remaining).toNat :=
        Nat.pos_of_ne_zero (fun zero => nonzero ((Word.toNat_eq_zero_iff _).mp zero))
      rw [decrease]
      have one : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
      change (BinOp.eval .sub (s.regs registers.remaining) 1).toNat <
        (s.regs registers.remaining).toNat
      rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [one]; omega), one]
      omega
  have cost : TimeBound control program heapLimit (depth + 1) iteration
      (fun s => completed s ∧ s.eval (.var registers.remaining) ≠ 0)
      (fun _ => Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget + 11) :=
    (iteration_timeBound registers lookup time).consequence
      (fun _ _ => trivial) (fun _ _ => Nat.le_refl _)
  have bound := TimeBound.while_linear completed
    (fun s => (s.regs registers.remaining).toNat)
    (Fold.Call.callSteps control f
      [.var registers.accumulator, .var registers.element] bodyBudget + 11)
    functional cost
  intro s _ steps finish execution
  have bounded := bound s ⟨_, execution.erase⟩ steps finish execution
  change steps ≤ (s.regs registers.remaining).toNat *
    (1 + 1 + (Fold.Call.callSteps control f
      [.var registers.accumulator, .var registers.element] bodyBudget + 11) + 1) +
    (1 + 1) at bounded
  have coefficient : 1 + 1 + (Fold.Call.callSteps control f
      [.var registers.accumulator, .var registers.element] bodyBudget + 11) + 1 =
      Fold.Call.callSteps control f
        [.var registers.accumulator, .var registers.element] bodyBudget + 14 := by omega
  rw [coefficient] at bounded
  simpa only [Nat.reduceAdd, Nat.mul_comm] using bounded

/-- The conditional bound for the complete iteration construct includes both
descriptor copies, all actual calls and loads, cursor writes and the final guard. -/
theorem forIn_timeBound (registers : Registers) {program : Program} {f : Func}
    {w control fn heapLimit depth bodyBudget : Nat} {base length : Expr} (hw : 0 < w)
    (lookup : program[fn]? = some f)
    (time : FunctionTimeBound (w := w) control program heapLimit depth f
      (fun args _ => args.length = 2) (fun _ _ => bodyBudget)) :
    TimeBound (w := w) control program heapLimit (depth + 1)
      (Stmt.forIn registers.pointer registers.remaining registers.element base length
        (body registers fn)) (fun _ => True)
      (fun s => (base.compile (ABI.scratch control)).length +
        (length.compile (ABI.scratch control)).length +
        (Fold.Call.callSteps control f [.var registers.accumulator, .var registers.element]
          bodyBudget + 14) *
          ((s.setReg registers.pointer (s.eval base)).eval length).toNat + 4) := by
  intro s _ steps finish execution
  cases execution with
  | seq first rest =>
    cases first with
    | assign _ =>
      cases rest with
      | seq second traversal =>
        cases second with
        | assign _ =>
          have bounded := loop_timeBound registers hw lookup time _ trivial _ _ traversal
          dsimp only at bounded ⊢
          simp only [State.setReg_same] at bounded
          simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
            List.length_append, List.length_singleton]
          omega

end Ram.Source.Array.ForIn.Call
