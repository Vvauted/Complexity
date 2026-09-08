/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic

/-!
# Parameter binding and returned local frames

Function arguments use ordinary list indexing. Return discards callee locals,
restores caller locals except the destinations, and retains the actual shared
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

/-- The register projection of ordered assignment is the corresponding ordinary
list fold; shared state is not part of the assignment. -/
theorem setRegs_regs (s : State w) (dsts : List Reg) (values : List (Word w)) :
    (s.setRegs dsts values).regs =
      (dsts.zip values).foldl
        (fun regs field => fun r => if r = field.1 then field.2 else regs r) s.regs :=
  (List.foldl_hom (fun t : State w => t.regs)
    (g₁ := fun (t : State w) (field : Reg × Word w) => t.setReg field.1 field.2)
    (g₂ := fun (regs : Reg → Word w) (field : Reg × Word w) =>
      fun r => if r = field.1 then field.2 else regs r)
    (l := dsts.zip values) (init := s) (fun _ _ => rfl)).symm

/-- Distinct destinations expose each field separately. Equal lengths prevent
truncation, while ordinary assignment itself also permits repeated destinations. -/
theorem setRegs_getElem (s : State w) (dsts : List Reg) (values : List (Word w))
    (distinct : dsts.Nodup) (hlength : dsts.length = values.length)
    (i : Nat) (hi : i < dsts.length) :
    (s.setRegs dsts values).regs dsts[i] = values[i]'(by omega) := by
  induction dsts generalizing s values i with
  | nil => simp at hi
  | cons dst dsts ih =>
      cases values with
      | nil => simp at hlength
      | cons value values =>
          have hd := List.nodup_cons.mp distinct
          have hlength' : dsts.length = values.length := by simpa using hlength
          cases i with
          | zero =>
              simp only [List.getElem_cons_zero, setRegs_cons]
              rw [setRegs_ne _ _ _ _ hd.1, setReg_same]
          | succ i =>
              have hi' : i < dsts.length := by simpa using hi
              simpa only [setRegs_cons, List.getElem_cons_succ] using
                ih (s.setReg dst value) values hd.2 hlength' i hi'

@[simp] theorem leave_nil (caller callee : State w) (results : List Expr) :
    caller.leave callee [] results = { callee with regs := caller.regs } := rfl

@[simp] theorem leave_singleton (caller callee : State w) (dst : Reg) (result : Expr) :
    caller.leave callee [dst] [result] =
      { callee with regs := caller.regs }.setReg dst (callee.eval result) := rfl

/-- Return fields are all observed in the original callee state, even when an
earlier caller destination has the same index as a later result expression. -/
theorem leave_getElem (caller callee : State w) (dsts : List Reg) (results : List Expr)
    (distinct : dsts.Nodup) (hlength : dsts.length = results.length)
    (i : Nat) (hi : i < dsts.length) :
    (caller.leave callee dsts results).regs dsts[i] =
      callee.eval (results[i]'(by omega)) := by
  simpa only [leave, List.getElem_map] using
    setRegs_getElem { callee with regs := caller.regs } dsts (results.map callee.eval)
      distinct (by simpa using hlength) i hi

/-- A call with unchanged shared memory and I/O is an ordered local assignment
of its actual returned fields. No callee-local preservation is required. -/
theorem leave_eq_setRegs_of_frame (caller callee : State w)
    (dsts : List Reg) (results : List Expr)
    (memory : callee.mem = caller.mem) (input : callee.input = caller.input)
    (output : callee.outputRev = caller.outputRev) :
    caller.leave callee dsts results = caller.setRegs dsts (results.map callee.eval) := by
  cases caller
  cases callee
  simp_all only [leave]

/-- A call with proved unchanged shared memory and I/O is precisely a local
assignment of its actual return value. Callee registers need not be preserved. -/
theorem leave_eq_setReg_of_frame (caller callee : State w) (dst : Reg) (result : Expr)
    (memory : callee.mem = caller.mem) (input : callee.input = caller.input)
    (output : callee.outputRev = caller.outputRev) :
    caller.leave callee [dst] [result] = caller.setReg dst (callee.eval result) := by
  simpa only [List.map_cons, List.map_nil, setRegs_singleton] using
    leave_eq_setRegs_of_frame caller callee [dst] [result] memory input output

/-- The callee's return register and the caller's destination can be different.
No other caller local or shared component changes for this endpoint. -/
@[simp] theorem leave_enter_setReg (s : State w) (args : List (Word w))
    (calleeReg dst : Reg) (value : Word w) :
    s.leave ((s.enter args).setReg calleeReg value) [dst] [.var calleeReg] =
      s.setReg dst value := by
  simp [leave, enter, setReg, eval, Expr.eval]

end Ram.Source.State
