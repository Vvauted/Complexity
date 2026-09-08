/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.ForIn
import Complexity.Computability.Ram.Array.Fold.Call

/-!
# Array iteration with a verified scalar function call

Each iteration loads an array element and passes that word and the accumulator
to a fixed source function. Its budget-free contract establishes the mathematical
step and preservation of shared state. The array-iteration rule supplies cursor
progress, termination and framing; no Lean callback is executed for free.

The separate exact-count theorem accepts a proved constant callee-body count.
The existing call compiler adds argument evaluation, frame handling and return
instructions, while the iteration rule counts initialization, loads and guards.
-/

namespace Ram.Source.Array.ForIn.Call

/-- The actual two-argument call after the iteration has loaded its element. -/
def body (registers : Registers) (fn : Nat) : Stmt :=
  .call registers.accumulator fn [.var registers.accumulator, .var registers.element]

/-- A verified source function implements one accumulator update on the loaded
word. Its returned value is assigned by the actual call instruction. -/
theorem body_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {step : Word w → Word w → Word w}
    (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = step accumulator x ∧ finish = entry))
    (s : State w) :
    SafeExec program heapLimit (depth + 1) (body registers fn) s
      (s.setReg registers.accumulator
        (step (s.regs registers.accumulator) (s.regs registers.element))) := by
  obtain ⟨value, finish, execution, rfl, rfl⟩ :=
    contract (s.regs registers.accumulator) (s.regs registers.element)
      [s.regs registers.accumulator, s.regs registers.element] s rfl
  exact execution.call lookup (by simp [Expr.ReadsBelow])

/-- Read a represented array through one fixed, verified function call per
element. The input expressions are evaluated in source order, and the frame
excludes the accumulator, element binding and both private cursor locals. -/
theorem forIn_safe (registers : Registers) {program : Program} {f : Func}
    {fn heapLimit depth : Nat} {base length : Expr} {step : Word w → Word w → Word w}
    (hw : 0 < w) (lookup : program[fn]? = some f)
    (contract : ∀ accumulator x, FunctionContract program heapLimit depth f
      (fun args _ => args = [accumulator, x])
      (fun _ entry value finish => value = step accumulator x ∧ finish = entry))
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
  | call _ _ _ _ _ _ =>
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
  | call found arity frame arguments callee result =>
    have same : _ = f := Option.some.inj (found.symm.trans lookup)
    subst f
    have count := cost callee
    have call := LocalMeasuredExec.call (dst := registers.accumulator)
      found arity frame arguments callee result
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

end Ram.Source.Array.ForIn.Call
