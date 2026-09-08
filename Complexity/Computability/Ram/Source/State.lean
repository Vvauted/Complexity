/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic

/-!
# Parameter binding and returned local frames

Function arguments use ordinary list indexing. Return discards callee locals,
restores caller locals except the destination, and retains the actual shared
memory and I/O effects. The frame rule below simplifies a pure call to a
register update only after all three shared-state equalities are proved.

These are equations about the existing source state, not a new calling
convention, evaluator, or cost model.
-/

namespace Ram.Source.State

@[simp] theorem enter_regs (s : State w) (args : List (Word w)) (r : Reg) :
    (s.enter args).regs r = args[r]?.getD 0 := rfl

/-- A parameter within the argument list has its ordinary list value. -/
theorem enter_regs_getElem (s : State w) (args : List (Word w)) (r : Reg)
    (h : r < args.length) : (s.enter args).regs r = args[r] := by
  simp only [enter_regs, List.getElem?_eq_getElem h, Option.getD_some]

/-- Non-parameter locals start at zero, rather than inheriting caller values. -/
theorem enter_regs_of_length_le (s : State w) (args : List (Word w)) (r : Reg)
    (h : args.length ≤ r) : (s.enter args).regs r = 0 := by
  simp only [enter_regs, List.getElem?_eq_none h, Option.getD_none]

@[simp] theorem setReg_setReg (s : State w) (r : Reg) (a b : Word w) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  simp only [setReg, State.mk.injEq, and_true]
  funext i
  by_cases h : i = r <;> simp [h]

/-- A call with proved unchanged shared memory and I/O is precisely a local
assignment of its actual return value. Callee registers need not be preserved. -/
theorem leave_eq_setReg_of_frame (caller callee : State w) (dst : Reg) (result : Expr)
    (memory : callee.mem = caller.mem) (input : callee.input = caller.input)
    (output : callee.outputRev = caller.outputRev) :
    caller.leave callee dst result = caller.setReg dst (callee.eval result) := by
  simp only [leave, setReg, memory, input, output]

/-- The callee's return register and the caller's destination can be different.
No other caller local or shared component changes for this endpoint. -/
@[simp] theorem leave_enter_setReg (s : State w) (args : List (Word w))
    (calleeReg dst : Reg) (value : Word w) :
    s.leave ((s.enter args).setReg calleeReg value) dst (.var calleeReg) =
      s.setReg dst value := by
  simp [leave, enter, setReg, eval, Expr.eval]

end Ram.Source.State
