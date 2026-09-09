/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Frame
import Complexity.Computability.Ram.Source.State.Frame

/-!
# Source executions with preserved shared state or streams

`Stmt.NoSharedWrites` excludes stores and stream operations. Expressions may
still read memory, so this condition does not assert that returned values are
independent of the heap. Calls are admitted provided every function body in the
program satisfies the same condition.

`Stmt.NoIOWrites` instead permits memory stores and preserves only the two
streams. A function can therefore return an updated heap without changing its
input or output stream.

Induction on the actual finite execution covers recursive and mutually recursive
calls without assuming their termination. The resulting local frame combines
shared-state preservation with the existing static register-frame theorem.
At a function boundary, restoring caller locals then recovers the whole entry
state. No instruction count or proposed time budget occurs in these results.
-/

namespace Ram

/-- A syntactic sufficient condition for preserving shared memory and both
streams. Calls require the separately stated condition on program bodies;
read-only expression evaluation is allowed. -/
def Stmt.NoSharedWrites : Stmt → Prop
  | .skip | .assign .. | .call .. => True
  | .seq first second => first.NoSharedWrites ∧ second.NoSharedWrites
  | .ite _ yes no => yes.NoSharedWrites ∧ no.NoSharedWrites
  | .while _ body => body.NoSharedWrites
  | .store .. | .read .. | .write .. => False

/-- A sufficient condition for retaining both streams while permitting actual
heap stores. Calls also require the condition on their program's bodies. -/
def Stmt.NoIOWrites : Stmt → Prop
  | .skip | .assign .. | .store .. | .call .. => True
  | .seq first second => first.NoIOWrites ∧ second.NoIOWrites
  | .ite _ yes no => yes.NoIOWrites ∧ no.NoIOWrites
  | .while _ body => body.NoIOWrites
  | .read .. | .write .. => False

namespace Source

/-- Actual finite execution of a stream-free statement preserves its input and
output, independently of changes to shared memory or local registers. -/
theorem Exec.streams_eq_of_noIOWrites {program : Program} {stmt : Stmt}
    {s t : State w} (execution : Exec program stmt s t)
    (programCondition : ∀ f ∈ program, f.body.NoIOWrites)
    (statementCondition : stmt.NoIOWrites) :
    t.input = s.input ∧ t.outputRev = s.outputRev := by
  induction execution with
  | skip | assign | store => exact ⟨rfl, rfl⟩
  | seq _ _ first second =>
      have firstStreams := first statementCondition.1
      have secondStreams := second statementCondition.2
      exact ⟨secondStreams.1.trans firstStreams.1, secondStreams.2.trans firstStreams.2⟩
  | iteTrue _ _ body => exact body statementCondition.1
  | iteFalse _ _ body => exact body statementCondition.2
  | whileFalse _ => exact ⟨rfl, rfl⟩
  | whileTrue _ _ _ body rest =>
      have bodyStreams := body statementCondition
      have restStreams := rest statementCondition
      exact ⟨restStreams.1.trans bodyStreams.1, restStreams.2.trans bodyStreams.2⟩
  | read _ | write => exact False.elim statementCondition
  | call lookup _ _ _ _ body =>
      simpa only [State.leave_input, State.leave_outputRev,
        State.enter_input, State.enter_outputRev] using
        body (programCondition _ (List.mem_of_getElem? lookup))

/-- Function return keeps the callee's actual heap while retaining both streams
when all executed bodies contain no stream operations. -/
theorem FunctionExec.streams_eq_of_noIOWrites {program : Program} {f : Func}
    {heapLimit depth : Nat} {args values : List (Word w)} {entry finish : State w}
    (execution : FunctionExec program heapLimit depth f args entry values finish)
    (programCondition : ∀ function ∈ program, function.body.NoIOWrites)
    (bodyCondition : f.body.NoIOWrites) :
    finish.input = entry.input ∧ finish.outputRev = entry.outputRev := by
  obtain ⟨_, _, callee, body, _, _, rfl⟩ := execution
  simpa only [State.restore_input, State.restore_outputRev,
    State.enter_input, State.enter_outputRev] using
    body.erase.streams_eq_of_noIOWrites programCondition bodyCondition

private theorem Exec.shared_eq_of_noSharedWrites {program : Program} {stmt : Stmt}
    {s t : State w} (execution : Exec program stmt s t)
    (programCondition : ∀ f ∈ program, f.body.NoSharedWrites) :
    stmt.NoSharedWrites →
      t.mem = s.mem ∧ t.input = s.input ∧ t.outputRev = s.outputRev := by
  induction execution with
  | skip => intro _; exact ⟨rfl, rfl, rfl⟩
  | assign => intro _; exact ⟨rfl, rfl, rfl⟩
  | store => intro impossible; exact False.elim impossible
  | seq _ _ first second =>
    rintro ⟨firstCondition, secondCondition⟩
    obtain ⟨firstMem, firstInput, firstOutput⟩ := first firstCondition
    obtain ⟨secondMem, secondInput, secondOutput⟩ := second secondCondition
    exact ⟨secondMem.trans firstMem, secondInput.trans firstInput,
      secondOutput.trans firstOutput⟩
  | iteTrue _ _ body => intro condition; exact body condition.1
  | iteFalse _ _ body => intro condition; exact body condition.2
  | whileFalse _ => intro _; exact ⟨rfl, rfl, rfl⟩
  | whileTrue _ _ _ body rest =>
    intro condition
    obtain ⟨bodyMem, bodyInput, bodyOutput⟩ := body condition
    obtain ⟨restMem, restInput, restOutput⟩ := rest condition
    exact ⟨restMem.trans bodyMem, restInput.trans bodyInput, restOutput.trans bodyOutput⟩
  | read _ => intro impossible; exact False.elim impossible
  | write => intro impossible; exact False.elim impossible
  | call lookup _ _ _ _ body =>
    intro _
    simpa only [State.leave_mem, State.leave_input, State.leave_outputRev,
      State.enter_mem, State.enter_input, State.enter_outputRev] using
      body (programCondition _ (List.mem_of_getElem? lookup))

/-- A completed statement without shared writes changes only its possible local
destinations. Program-wide body conditions include recursive callees. -/
theorem Exec.localFrame_of_noSharedWrites {program : Program} {stmt : Stmt}
    {s t : State w} (execution : Exec program stmt s t)
    (programCondition : ∀ f ∈ program, f.body.NoSharedWrites)
    (statementCondition : stmt.NoSharedWrites) :
    State.LocalFrame stmt.writtenRegs s t := by
  obtain ⟨memory, input, output⟩ :=
    execution.shared_eq_of_noSharedWrites programCondition statementCondition
  refine ⟨memory, input, output, ?_⟩
  intro r outside
  exact execution.regs_eq_of_not_mem_writtenRegs outside

/-- Heap-safe execution inherits the same local frame by erasing its safety
premises, without another induction or a callee termination assumption. -/
theorem SafeExec.localFrame_of_noSharedWrites {program : Program} {stmt : Stmt}
    {heapLimit depth : Nat} {s t : State w}
    (execution : SafeExec program heapLimit depth stmt s t)
    (programCondition : ∀ f ∈ program, f.body.NoSharedWrites)
    (statementCondition : stmt.NoSharedWrites) :
    State.LocalFrame stmt.writtenRegs s t :=
  execution.erase.localFrame_of_noSharedWrites programCondition statementCondition

/-- The same function invocation restores its entire entry state when its body
and every callable body have no shared writes. Result fields remain separately
returned by the original execution; the top-level function need not be a table member. -/
theorem FunctionExec.finish_eq_of_noSharedWrites {program : Program} {f : Func}
    {heapLimit depth : Nat} {args values : List (Word w)} {entry finish : State w}
    (execution : FunctionExec program heapLimit depth f args entry values finish)
    (programCondition : ∀ function ∈ program, function.body.NoSharedWrites)
    (bodyCondition : f.body.NoSharedWrites) : finish = entry := by
  obtain ⟨_, _, callee, body, _, _, rfl⟩ := execution
  have frame := body.localFrame_of_noSharedWrites programCondition bodyCondition
  exact State.restore_eq_of_shared frame.mem frame.input frame.outputRev

end Source
end Ram
