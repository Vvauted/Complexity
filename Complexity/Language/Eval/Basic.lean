/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Semantics
import Mathlib.Data.Part

/-!
# Independent source results as partial values

`Stmt.eval` observes every finite execution of the independent source syntax:
normal continuation, actual return and fault remain distinct. No finite outcome
means the partial value is undefined. `Program.eval` applies the function
boundary, turning body fallthrough into `Fault.missingReturn` rather than a
default value, including for Unit functions.

These are noncomputable semantic observations using mathlib's `Part`, not an
additional executable interpreter. The observed value is fixed by source
determinism, not selected from a mathematical specification. Neither the
definition nor its adequacy lemmas import RAM, a word width or a proposed budget.
-/

namespace Complexity.Language

namespace Stmt

/-- The complete finite outcome of a source statement. Faults are observations;
they are not identified with the absence of any finite execution. -/
noncomputable def eval {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (stmt : Stmt signatures Γ result) (program : Program signatures) (entry : Env Γ) :
    Part (Env Γ × Control result) where
  Dom := ∃ outcome : Env Γ × Control result,
    Exec program stmt entry outcome.1 outcome.2
  get := fun h => h.choose

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {stmt : Stmt signatures Γ result} {program : Program signatures} {entry : Env Γ}

/-- Membership is exactly finite source execution, including its control result. -/
theorem mem_eval_iff {outcome : Env Γ × Control result} :
    outcome ∈ stmt.eval program entry ↔ Exec program stmt entry outcome.1 outcome.2 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro execution
    have defined : (stmt.eval program entry).Dom := ⟨outcome, execution⟩
    refine ⟨defined, ?_⟩
    obtain ⟨sameEnv, sameControl⟩ := defined.choose_spec.deterministic execution
    exact Prod.ext sameEnv sameControl

/-- A defined result equation includes finite execution, not just an implication
about what a terminating statement might return. -/
theorem eval_eq_some_iff {outcome : Env Γ × Control result} :
    stmt.eval program entry = Part.some outcome ↔ Exec program stmt entry outcome.1 outcome.2 :=
  Part.eq_some_iff.trans mem_eval_iff

/-- Undefinedness means there is no finite source outcome, including no fault. -/
theorem eval_eq_none_iff :
    stmt.eval program entry = Part.none ↔
      ¬∃ finish control, Exec program stmt entry finish control := by
  rw [Part.eq_none_iff']
  simp only [eval, Prod.exists]

end Stmt

/-- A finite source execution determines the semantic result without changing
its final lexical environment or control outcome. -/
theorem Exec.eval_eq_some {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {entry finish : Env Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) :
    stmt.eval program entry = Part.some (finish, control) :=
  Stmt.eval_eq_some_iff.mpr execution

/-- Interpret a statement's control at a function boundary. Fallthrough is a
missing-return fault even when the declared return type is Unit. -/
def Control.toExcept {result : Ty} : Control result → Except Fault (Value result)
  | .normal => .error .missingReturn
  | .returned value => .ok value
  | .fault error => .error error

@[simp] theorem Control.toExcept_eq_ok_iff {result : Ty} (control : Control result)
    (value : Value result) : control.toExcept = .ok value ↔ control = .returned value := by
  cases control <;> simp [Control.toExcept]

namespace Program

/-- The actual function result, retaining finite faults separately from
divergence. Arguments and returned values are ordinary Lean mathematical values. -/
noncomputable def eval {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) (args : Env signatures[fn].params) :
    Part (Except Fault (Value signatures[fn].result)) :=
  ((program.body fn).eval program args).map (fun outcome => outcome.2.toExcept)

variable {signatures : List Signature} {program : Program signatures}
variable {fn : Fin signatures.length} {args : Env signatures[fn].params}

/-- A successful partial result is exactly a real returned source execution. -/
theorem mem_eval_ok_iff {value : Value signatures[fn].result} :
    Except.ok value ∈ program.eval fn args ↔
      ∃ finish, Exec program (program.body fn) args finish (.returned value) := by
  constructor
  · intro member
    obtain ⟨⟨finish, control⟩, execution, returned⟩ := Part.mem_map_iff _ |>.mp member
    have same : control = .returned value := (Control.toExcept_eq_ok_iff _ _).mp returned
    exact ⟨finish, same ▸ Stmt.mem_eval_iff.mp execution⟩
  · rintro ⟨finish, execution⟩
    exact Part.mem_map_iff _ |>.mpr
      ⟨(finish, .returned value), Stmt.mem_eval_iff.mpr execution, rfl⟩

/-- A successful result equation includes source termination and the exact value. -/
theorem eval_eq_ok_iff {value : Value signatures[fn].result} :
    program.eval fn args = Part.some (.ok value) ↔
      ∃ finish, Exec program (program.body fn) args finish (.returned value) :=
  Part.eq_some_iff.trans mem_eval_ok_iff

/-- A finite fault result includes either body fallthrough or an actual fault;
neither case is silently treated as divergence. -/
theorem eval_eq_error_iff {error : Fault} :
    program.eval fn args = Part.some (.error error) ↔
      (error = .missingReturn ∧ ∃ finish, Exec program (program.body fn) args finish .normal) ∨
        ∃ finish, Exec program (program.body fn) args finish (.fault error) := by
  rw [Part.eq_some_iff]
  constructor
  · intro member
    obtain ⟨⟨finish, control⟩, execution, returned⟩ := Part.mem_map_iff _ |>.mp member
    have execution := Stmt.mem_eval_iff.mp execution
    cases control with
    | normal => exact Or.inl ⟨(Except.error.inj returned).symm, finish, execution⟩
    | returned value => cases returned
    | fault fault =>
        cases Except.error.inj returned
        exact Or.inr ⟨finish, execution⟩
  · rintro (⟨rfl, finish, execution⟩ | ⟨finish, execution⟩)
    · exact Part.mem_map_iff _ |>.mpr
        ⟨(finish, .normal), Stmt.mem_eval_iff.mpr execution, rfl⟩
    · exact Part.mem_map_iff _ |>.mpr
        ⟨(finish, .fault error), Stmt.mem_eval_iff.mpr execution, rfl⟩

/-- The function observation is undefined exactly when its body has no finite
outcome. Body fallthrough and finite faults are defined error results. -/
theorem eval_eq_none_iff :
    program.eval fn args = Part.none ↔
      ¬∃ finish control, Exec program (program.body fn) args finish control := by
  rw [Part.eq_none_iff']
  change (¬∃ outcome : Env signatures[fn].params × Control signatures[fn].result,
    Exec program (program.body fn) args outcome.1 outcome.2) ↔ _
  simp only [Prod.exists]

end Program

end Complexity.Language
