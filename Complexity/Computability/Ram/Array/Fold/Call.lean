/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Fold
import Complexity.Computability.Ram.Source.Function.Time

/-!
# Read-only array folds with a verified function call at each step

`Fold.Call.loop_safe` reuses the array cursor and ordinary `List.foldl` rule.
Its fixed body calls a concrete function from the source program; that
function's budget-free contract implements the mathematical accumulator step.
Argument expressions, including loads, execute in the caller. The callee must
preserve shared state, and its caller locals are restored by the existing ABI.

Correctness requires no time bound. The separate exact-count rule accepts a
proved constant callee-body count and adds the actual argument, frame, return,
cursor and loop instructions. It does not price a mathematical callback or
cover state-dependent callee costs; the general `TimeBound` composition rules
remain available for those bounds.
-/

namespace Ram.Source.Array.Fold.Call

/-- A fixed call computes the next accumulator before the cursor advances. -/
def body (registers : Registers) (fn : Nat) (args : List Expr) : Stmt :=
  .seq (.call [registers.accumulator] fn args) (advanceCursor registers)

/-- The same call site is executed for every represented element. -/
def loop (registers : Registers) (fn : Nat) (args : List Expr) : Stmt :=
  .while (.var registers.remaining) (body registers fn args)

/-- One step uses an actual function contract, including its shared-state
guarantee. The mathematical accumulator update specifies the returned value. -/
theorem body_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {args : List Expr}
    {step : Word w → Word w → Word w}
    {P : Word w → Word w → List (Word w) → State w → Prop}
    (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f (P accumulator x)
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (s : State w)
    (reads : ∀ arg ∈ args, arg.ReadsBelow heapLimit s.regs s.mem)
    (pre : P (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))
      (args.map s.eval) s) :
    SafeExec program heapLimit (depth + 1) (body registers fn args) s
      (advanceState registers
        (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    contract _ _ (args.map s.eval) s pre
  have resultCount : [registers.accumulator].length = f.results.length := by
    simpa only [List.length_cons, List.length_nil] using execution.length_eq
  exact .seq (execution.call (dsts := [registers.accumulator]) lookup resultCount reads)
    (advanceCursor_safe registers _ _)

/-- Fold a represented list through one fixed, verified function call. The
contract and argument adapter implement each mathematical step; cursor safety,
termination and framing are supplied by the shared traversal rule. -/
theorem loop_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {args : List Expr}
    {step : Word w → Word w → Word w} {R : State w → Prop}
    {P : Word w → Word w → List (Word w) → State w → Prop}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f (P accumulator x)
      (fun _ entry value finish => value = [step accumulator x] ∧ finish = entry))
    (reads : ∀ s, R s → (s.regs registers.pointer).toNat < heapLimit →
      ∀ arg ∈ args, arg.ReadsBelow heapLimit s.regs s.mem)
    (pre : ∀ s, R s → (s.regs registers.pointer).toNat < heapLimit →
      P (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))
        (args.map s.eval) s)
    (preserve : ∀ s, R s → R (advanceState registers
      (step (s.regs registers.accumulator) (s.mem (s.regs registers.pointer))) s))
    (s : State w) (base : Word w) (xs : List (Word w)) (invariant : R s)
    (represented : ArrayRep s.mem base xs) (pointer : s.regs registers.pointer = base)
    (count : (s.regs registers.remaining).toNat = xs.length)
    (heap : base.toNat + xs.length ≤ heapLimit) (fit : base.toNat + xs.length < 2 ^ w) :
    ∃ t, SafeExec program heapLimit (depth + 1) (loop registers fn args) s t ∧
      t.regs registers.accumulator = xs.foldl step (s.regs registers.accumulator) ∧
      t.regs registers.pointer = arrayAddr base xs.length ∧ t.regs registers.remaining = 0 ∧
      R t ∧ t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev ∧
      ∀ r, r ≠ registers.pointer → r ≠ registers.remaining →
        r ≠ registers.accumulator → t.regs r = s.regs r :=
  loop_safe_of_step registers hw
    (fun current hR address => body_safe registers lookup contract current
      (reads current hR address) (pre current hR address))
    preserve s base xs invariant represented pointer count heap fit

/-- The caller's remaining word survives the callee and is then decremented.
This fact depends only on the actual call and cursor assignments, not the
callee's functional specification or its shared-memory behavior. -/
theorem body_remaining (registers : Registers) {program : Program}
    {fn heapLimit depth : Nat} {args : List Expr} {s t : State w}
    (h : SafeExec program heapLimit depth (body registers fn args) s t) :
    t.regs registers.remaining = s.regs registers.remaining - 1 := by
  cases h with
  | seq first rest =>
    cases first with
    | call _ _ _ _ _ _ _ =>
      simpa [State.leave, registers.remaining_ne_accumulator] using
        advanceCursor_remaining registers rest

/-- The real call instruction blocks surrounding a separately measured body.
The scalar fold receives one field; its safe call proves that the helper returns
exactly one field. All helper return expressions are still charged here. -/
def callSteps (control : Nat) (f : Func) (args : List Expr) (bodySteps : Nat) : Nat :=
  (ABI.callPrefixLocals control f.locals args 0).length + 1 + bodySteps +
    (ABI.returnCodeResultsLocals control f.locals f.results).length + 1

/-- Reduce the actual call count using the compiler's existing code-length
identity. Return-expression evaluation is included, even for an empty body. -/
theorem callSteps_eq (control : Nat) (f : Func) (args : List Expr) (bodySteps : Nat) :
    callSteps control f args bodySteps =
      (args.map (fun e => (e.compile (ABI.scratch control)).length)).sum + bodySteps +
        (f.results.map (fun result => (result.compile (ABI.scratch control)).length)).sum +
        7 * f.locals + args.length + f.results.length + 10 := by
  rw [callSteps, ABI.callPrefixLocals_length_eq, ABI.returnCodeResultsLocals_length]
  omega

/-- The concrete iteration includes the full call and eight cursor instructions.
The callee count is a theorem about every completed execution of its body. -/
theorem body_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat} {args : List Expr}
    (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1) (body registers fn args) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1) (body registers fn args)
      (callSteps control f args bodySteps + 8) s t := by
  cases h with
  | seq first rest =>
    obtain ⟨steps, measured⟩ := first.exists_localMeasured control
    cases measured with
    | call found arity resultCount frame arguments callee results =>
      have same : _ = f := Option.some.inj (found.symm.trans lookup)
      subst f
      have count := cost callee
      have call := LocalMeasuredExec.call (dsts := [registers.accumulator])
        found arity resultCount frame arguments callee results
      rw [count] at call
      exact .seq call (advanceCursor_localMeasured registers rest)

/-- An exact constant callee-body count yields the loop's actual linear count.
Correctness is independent: this theorem starts with a completed safe loop
and adds call overhead, cursor writes, true guards, backedges and final guard. -/
theorem loop_localMeasured (registers : Registers) {program : Program} {f : Func}
    {control fn heapLimit depth bodySteps : Nat} {args : List Expr}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (cost : ∀ {s t : State w} {steps},
      LocalMeasuredExec control program heapLimit depth f.body steps s t → steps = bodySteps)
    {s t : State w}
    (h : SafeExec program heapLimit (depth + 1) (loop registers fn args) s t) :
    LocalMeasuredExec control program heapLimit (depth + 1) (loop registers fn args)
      ((callSteps control f args bodySteps + 11) * (s.regs registers.remaining).toNat + 2) s t :=
  loop_localMeasured_of_body registers hw (body_remaining registers)
    (body_localMeasured registers lookup cost) h

end Ram.Source.Array.Fold.Call
