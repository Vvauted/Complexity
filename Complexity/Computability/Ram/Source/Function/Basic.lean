/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Safe
import Complexity.Computability.Ram.Source.State

/-!
# Function arguments, returned values and shared effects

`Ram.Source.FunctionExec` describes an invocation of an actual `Ram.Func`, without
an input/output wrapper or caller destination registers. Arguments initialize
the existing local frame; the body executes with `Ram.Source.SafeExec`, and the
return expressions determine the returned fields in that same callee state.
The resulting state restores the caller's registers and retains the callee's
memory and input/output effects.

This is an observation of the existing execution relation, not an evaluator or
a mathematical specification substituted for the program. Heap and call-depth
capacities are safety premises; correctness requires no instruction budget.
-/

namespace Ram.Source

namespace State

/-- Restore caller locals while retaining the callee's shared effects. A caller
may subsequently assign the separately returned fields to its destinations. -/
def restore (caller callee : State w) : State w :=
  { callee with regs := caller.regs }

@[simp] theorem restore_regs (caller callee : State w) :
    (caller.restore callee).regs = caller.regs := rfl

@[simp] theorem restore_mem (caller callee : State w) :
    (caller.restore callee).mem = callee.mem := rfl

@[simp] theorem restore_input (caller callee : State w) :
    (caller.restore callee).input = callee.input := rfl

@[simp] theorem restore_outputRev (caller callee : State w) :
    (caller.restore callee).outputRev = callee.outputRev := rfl

/-- Assigning the returned fields is exactly the existing call-return state. -/
theorem restore_setRegs (caller callee : State w) (dsts : List Reg) (results : List Expr) :
    (caller.restore callee).setRegs dsts (results.map callee.eval) =
      caller.leave callee dsts results := rfl

end State

/-- Safe invocation with explicit arguments and return fields. `depth` bounds
calls inside the body; invoking this function from another body uses one more
level. The final state has the original caller locals and actual shared effects. -/
def FunctionExec (program : Program) (heapLimit depth : Nat) (f : Func)
    (args : List (Word w)) (entry : State w) (value : List (Word w)) (finish : State w) : Prop :=
  args.length = f.params ∧ f.params ≤ f.locals ∧
    ∃ callee, SafeExec program heapLimit depth f.body (entry.enter args) callee ∧
      (∀ result ∈ f.results, result.ReadsBelow heapLimit callee.regs callee.mem) ∧
      value = f.results.map callee.eval ∧ finish = entry.restore callee

namespace FunctionExec

variable {w heapLimit depth : Nat} {program : Program} {f : Func}
variable {args : List (Word w)} {entry finish : State w} {value : List (Word w)}

/-- Expose the actual return fields and shared effects of a proved body run. -/
theorem of_body {callee : State w} (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (body : SafeExec program heapLimit depth f.body (entry.enter args) callee)
    (result : ∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) :
    FunctionExec program heapLimit depth f args entry (f.results.map callee.eval)
      (entry.restore callee) :=
  ⟨arity, frame, callee, body, result, rfl, rfl⟩

/-- An invocation returns exactly the function's declared number of fields. -/
theorem length_eq (h : FunctionExec program heapLimit depth f args entry value finish) :
    value.length = f.results.length := by
  obtain ⟨_, _, _, _, _, rfl, _⟩ := h
  simp only [List.length_map]

/-- The caller's local variables are not callee output. -/
theorem regs_eq (h : FunctionExec program heapLimit depth f args entry value finish) :
    finish.regs = entry.regs := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := h
  rfl

/-- A safe invocation preserves source memory outside its heap boundary. -/
theorem mem_eq_of_le (h : FunctionExec program heapLimit depth f args entry value finish)
    (address : Word w) (haddr : heapLimit ≤ address.toNat) :
    finish.mem address = entry.mem address := by
  obtain ⟨_, _, callee, body, _, _, rfl⟩ := h
  exact body.mem_eq_of_le address haddr

/-- Safety capacities do not affect either the returned value or shared effects. -/
theorem deterministic {heapLimit' depth' : Nat} {value' : List (Word w)} {finish' : State w}
    (h : FunctionExec program heapLimit depth f args entry value finish)
    (h' : FunctionExec program heapLimit' depth' f args entry value' finish') :
    value = value' ∧ finish = finish' := by
  obtain ⟨_, _, callee, body, _, rfl, rfl⟩ := h
  obtain ⟨_, _, callee', body', _, rfl, rfl⟩ := h'
  have same := body.deterministic body'
  subst callee'
  exact ⟨rfl, rfl⟩

/-- Additional allowed nesting does not alter the invocation. -/
theorem mono_depth {depth' : Nat}
    (h : FunctionExec program heapLimit depth f args entry value finish)
    (hd : depth ≤ depth') :
    FunctionExec program heapLimit depth' f args entry value finish := by
  obtain ⟨arity, frame, callee, body, result, returned, shared⟩ := h
  exact ⟨arity, frame, callee, body.mono hd, result, returned, shared⟩

/-- Use the invocation at an actual source call. Argument expressions are
evaluated in the caller; lookup and argument-read safety remain explicit. -/
theorem call {fn : Nat} {dsts : List Reg} {exprs : List Expr}
    (h : FunctionExec program heapLimit depth f (exprs.map entry.eval) entry value finish)
    (lookup : program[fn]? = some f)
    (resultCount : dsts.length = f.results.length)
    (arguments : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem) :
    SafeExec program heapLimit (depth + 1) (.call dsts fn exprs) entry
      (finish.setRegs dsts value) := by
  obtain ⟨arity, frame, callee, body, result, rfl, rfl⟩ := h
  rw [State.restore_setRegs]
  exact .call lookup (by simpa only [List.length_map] using arity) resultCount frame
    arguments body result

end FunctionExec

end Ram.Source
