/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Function.Time
import Mathlib.Data.Part

/-!
# Function results and costs as partial values

`Ram.Func.eval` observes the returned fields and shared state of an actual function
invocation. Its domain is safe termination for some finite call depth, not a
proposed instruction budget. `Ram.Func.bodyTime` independently observes the
compiler-derived body count of that same invocation. Both use mathlib's `Part`;
their values are uniquely determined by execution, not by a specification.

These are noncomputable semantic observations, not a source interpreter or a
compiler for ordinary Lean definitions. The heap boundary remains explicit:
insufficient capacity can make an observation undefined. Arguments alone do not
determine a general stateful function's result, so the entry state is retained.
Clients may hide it only after proving the relevant representation independence.

Mapping a mathematical decoder over a result is a proof view, not executable
data conversion. Body time includes nested calls but excludes the enclosing
call's argument evaluation, frame setup and return sequence.
-/

namespace Ram

namespace Func

/-- The result of a safely terminating invocation, with call depth existentially
hidden. No mathematical result function or time bound is supplied. -/
noncomputable def eval (f : Func) (program : Program) (heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) : Part (List (Word w) × Source.State w) where
  Dom := ∃ result : List (Word w) × Source.State w, ∃ depth,
    Source.FunctionExec program heapLimit depth f args entry result.1 result.2
  get := fun h => h.choose

variable {w heapLimit depth : Nat} {f : Func} {program : Program}
variable {args : List (Word w)} {entry finish : Source.State w} {value : List (Word w)}

/-- Membership describes exactly the existing safe execution relation. -/
theorem mem_eval_iff {result : List (Word w) × Source.State w} :
    result ∈ f.eval program heapLimit args entry ↔
      ∃ depth, Source.FunctionExec program heapLimit depth f args entry result.1 result.2 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · rintro ⟨depth, execution⟩
    have h : (f.eval program heapLimit args entry).Dom := ⟨result, depth, execution⟩
    refine ⟨h, ?_⟩
    obtain ⟨chosenDepth, chosen⟩ := h.choose_spec
    exact Prod.ext (chosen.deterministic execution).1 (chosen.deterministic execution).2

/-- An equation with `Part.some` includes termination as well as the result. -/
theorem eval_eq_some_iff {result : List (Word w) × Source.State w} :
    f.eval program heapLimit args entry = Part.some result ↔
      ∃ depth, Source.FunctionExec program heapLimit depth f args entry result.1 result.2 :=
  Part.eq_some_iff.trans mem_eval_iff

/-- Every observed result has exactly the function's declared number of fields. -/
theorem mem_eval_length {result : List (Word w) × Source.State w}
    (h : result ∈ f.eval program heapLimit args entry) :
    result.1.length = f.results.length := by
  obtain ⟨_, execution⟩ := mem_eval_iff.mp h
  exact execution.length_eq

/-- Attach the proved field count to the same partial observation. Typed result
decoders can then read actual fields without supplying defaults or extra values. -/
noncomputable def evalFields (f : Func) (program : Program) (heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) :
    Part ({values : List (Word w) // values.length = f.results.length} × Source.State w) where
  Dom := (f.eval program heapLimit args entry).Dom
  get := fun h =>
    ⟨⟨((f.eval program heapLimit args entry).get h).1, mem_eval_length (Part.get_mem h)⟩,
      ((f.eval program heapLimit args entry).get h).2⟩

/-- Attaching field-count evidence changes neither termination nor shared effects. -/
@[simp] theorem evalFields_dom :
    (f.evalFields program heapLimit args entry).Dom ↔
      (f.eval program heapLimit args entry).Dom := Iff.rfl

/-- Forgetting field-count evidence recovers exactly the original observation. -/
@[simp] theorem evalFields_map :
    (f.evalFields program heapLimit args entry).map
      (fun result => (result.1.val, result.2)) = f.eval program heapLimit args entry := rfl

theorem mem_evalFields_iff
    {fields : {values : List (Word w) // values.length = f.results.length}} :
    (fields, finish) ∈ f.evalFields program heapLimit args entry ↔
      (fields.val, finish) ∈ f.eval program heapLimit args entry := by
  constructor
  · rintro ⟨h, equal⟩
    exact ⟨h, congrArg (fun result => (result.1.val, result.2)) equal⟩
  · rintro ⟨h, equal⟩
    have fieldsEqual := congrArg (fun result : List (Word w) × Source.State w => result.1) equal
    have stateEqual := congrArg (fun result : List (Word w) × Source.State w => result.2) equal
    exact ⟨h, Prod.ext (Subtype.ext fieldsEqual) stateEqual⟩

/-- Typed decoding uses the original result equation, with no new execution proof. -/
theorem evalFields_eq_some_iff
    {fields : {values : List (Word w) // values.length = f.results.length}} :
    f.evalFields program heapLimit args entry = Part.some (fields, finish) ↔
      f.eval program heapLimit args entry = Part.some (fields.val, finish) :=
  Part.eq_some_iff.trans (mem_evalFields_iff.trans Part.eq_some_iff.symm)

/-- Reuse a raw result equation through the field-count interface. -/
theorem evalFields_eq_some
    (h : f.eval program heapLimit args entry = Part.some (value, finish))
    (length : value.length = f.results.length) :
    f.evalFields program heapLimit args entry = Part.some (⟨value, length⟩, finish) :=
  evalFields_eq_some_iff.mpr h

/-- Increasing safe heap capacity preserves every already defined result. -/
theorem eval_mono_heap {heapLimit' : Nat} {result : List (Word w) × Source.State w}
    (h : result ∈ f.eval program heapLimit args entry) (hh : heapLimit ≤ heapLimit') :
    result ∈ f.eval program heapLimit' args entry := by
  obtain ⟨depth, execution⟩ := mem_eval_iff.mp h
  exact mem_eval_iff.mpr ⟨depth, execution.mono_heap hh⟩

/-- The exact compiled body count, observed without proposing a bound. -/
noncomputable def bodyTime (f : Func) (program : Program) (heapLimit : Nat)
    (args : List (Word w)) (entry : Source.State w) : Part Nat where
  Dom := ∃ steps control depth value finish,
    Source.FunctionMeasuredExec control program heapLimit depth f args steps entry value finish
  get := fun h => h.choose

/-- Time membership is an actual measured invocation, not an upper bound. -/
theorem mem_bodyTime_iff {steps : Nat} :
    steps ∈ f.bodyTime program heapLimit args entry ↔
      ∃ control depth value finish,
        Source.FunctionMeasuredExec control program heapLimit depth f args steps
          entry value finish := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · rintro ⟨control, depth, value, finish, execution⟩
    have h : (f.bodyTime program heapLimit args entry).Dom :=
      ⟨steps, control, depth, value, finish, execution⟩
    refine ⟨h, ?_⟩
    obtain ⟨chosenControl, chosenDepth, chosenValue, chosenFinish, chosen⟩ := h.choose_spec
    exact (chosen.deterministic execution).1

theorem bodyTime_eq_some_iff {steps : Nat} :
    f.bodyTime program heapLimit args entry = Part.some steps ↔
      ∃ control depth value finish,
        Source.FunctionMeasuredExec control program heapLimit depth f args steps
          entry value finish :=
  Part.eq_some_iff.trans mem_bodyTime_iff

/-- Result and time are defined on precisely the same safe invocations. -/
theorem bodyTime_dom_iff_eval_dom :
    (f.bodyTime program heapLimit args entry).Dom ↔
      (f.eval program heapLimit args entry).Dom := by
  constructor
  · rintro ⟨steps, control, depth, value, finish, execution⟩
    exact ⟨(value, finish), depth, execution.erase⟩
  · rintro ⟨⟨value, finish⟩, depth, execution⟩
    obtain ⟨steps, measured⟩ := execution.exists_measured f.locals
    exact ⟨steps, f.locals, depth, value, finish, measured⟩

/-- Separately observed results and costs belong to one and the same execution. -/
theorem eval_bodyTime_iff {result : List (Word w) × Source.State w} {steps : Nat} :
    (f.eval program heapLimit args entry = Part.some result ∧
      f.bodyTime program heapLimit args entry = Part.some steps) ↔
      ∃ control depth,
        Source.FunctionMeasuredExec control program heapLimit depth f args steps
          entry result.1 result.2 := by
  constructor
  · rintro ⟨resultEq, timeEq⟩
    obtain ⟨resultDepth, resultExec⟩ := eval_eq_some_iff.mp resultEq
    obtain ⟨control, depth, value, finish, measured⟩ := bodyTime_eq_some_iff.mp timeEq
    obtain ⟨rfl, rfl⟩ := resultExec.deterministic measured.erase
    exact ⟨control, depth, measured⟩
  · rintro ⟨control, depth, measured⟩
    exact ⟨eval_eq_some_iff.mpr ⟨depth, measured.erase⟩,
      bodyTime_eq_some_iff.mpr ⟨control, depth, _, _, measured⟩⟩

end Func

namespace Source

variable {w control heapLimit depth : Nat} {f : Func} {program : Program}
variable {args : List (Word w)} {entry finish : State w} {value : List (Word w)}

/-- Turn a safe invocation into a function-value equation. -/
theorem FunctionExec.eval_eq_some
    (h : FunctionExec program heapLimit depth f args entry value finish) :
    f.eval program heapLimit args entry = Part.some (value, finish) :=
  Func.eval_eq_some_iff.mpr ⟨depth, h⟩

/-- Turn a measured invocation into its independently defined time observation. -/
theorem FunctionMeasuredExec.bodyTime_eq_some {steps : Nat}
    (h : FunctionMeasuredExec control program heapLimit depth f args steps entry value finish) :
    f.bodyTime program heapLimit args entry = Part.some steps :=
  Func.bodyTime_eq_some_iff.mpr ⟨control, depth, value, finish, h⟩

/-- A function contract yields a defined semantic value satisfying its ordinary
mathematical postcondition; the postcondition need not define a reference algorithm. -/
theorem FunctionContract.eval_spec {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    (h : FunctionContract program heapLimit depth f P Q) (hp : P args entry) :
    ∃ value finish, f.eval program heapLimit args entry = Part.some (value, finish) ∧
      Q args entry value finish := by
  obtain ⟨value, finish, execution, post⟩ := h args entry hp
  exact ⟨value, finish, execution.eval_eq_some, post⟩

/-- A total contract controls every value observed through the semantic interface. -/
theorem FunctionContract.eval_post {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    (h : FunctionContract program heapLimit depth f P Q) (hp : P args entry)
    (result : (value, finish) ∈ f.eval program heapLimit args entry) :
    Q args entry value finish := by
  obtain ⟨resultDepth, execution⟩ := Func.mem_eval_iff.mp result
  exact h.post hp execution

/-- Publish a result property and a separately proved bound as observations of
the same invocation. Neither observation is defined using those proposed properties. -/
theorem FunctionContract.eval_with_timeBound {P : List (Word w) → State w → Prop}
    {Q : List (Word w) → State w → List (Word w) → State w → Prop}
    {bound : List (Word w) → State w → Nat}
    (h : FunctionContract program heapLimit depth f P Q)
    (time : FunctionTimeBound control program heapLimit depth f P bound) (hp : P args entry) :
    ∃ steps value finish,
      f.eval program heapLimit args entry = Part.some (value, finish) ∧
      f.bodyTime program heapLimit args entry = Part.some steps ∧
      Q args entry value finish ∧ steps ≤ bound args entry := by
  obtain ⟨steps, value, finish, execution, post, bound⟩ := h.with_timeBound time args entry hp
  exact ⟨steps, value, finish, execution.erase.eval_eq_some,
    execution.bodyTime_eq_some, post, bound⟩

/-- Apply a separate bound to the observed count using a terminating execution
at the bound's declared depth. The time-bound premise alone does not supply it. -/
theorem FunctionTimeBound.bodyTime_le {P : List (Word w) → State w → Prop}
    {bound : List (Word w) → State w → Nat} {steps : Nat}
    (h : FunctionTimeBound control program heapLimit depth f P bound) (hp : P args entry)
    (execution : FunctionExec program heapLimit depth f args entry value finish)
    (time : steps ∈ f.bodyTime program heapLimit args entry) :
    steps ≤ bound args entry := by
  obtain ⟨actualSteps, measured⟩ := execution.exists_measured control
  obtain ⟨observedControl, observedDepth, observedValue, observedFinish, observed⟩ :=
    Func.mem_bodyTime_iff.mp time
  have equal := (observed.deterministic measured).1
  rw [equal]
  exact h args entry hp actualSteps value finish measured

end Source
end Ram
