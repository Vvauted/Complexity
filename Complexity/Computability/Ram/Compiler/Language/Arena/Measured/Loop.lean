/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Loop.Models
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured

/-!
# Loop readiness from measured mathematical rounds

Existing guard and body measurements compose through the mathematical loop
rule without client-side coordinate transport or execution-witness unpacking.
Their postconditions establish the resource invariant using the source
contract's observation at the actual final heap. The representation need not
determine a runtime handle, and guards need not leave the heap or cursor fixed.

The supplied finite loop execution still provides termination. This interface
reuses the existing indexed readiness rule; it neither repeats loop induction
nor introduces an instruction budget or a new cost semantics. Algorithmic
invariants, word ranges and capacity remain supplied obligations.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

universe u

/-- Compose existing measured rounds with their mathematical source contracts.
The source observations feed resource preservation at each actual final heap
and cursor. The body contract excludes early returns; the guard preserves the
mathematical model, but neither fragment is required to preserve the heap. -/
theorem while_model_of_measured {Model : Type u}
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {Γ : List Ty} {result : Ty} {Locals : Type}
    {w heapLimit depth cursor : Nat}
    {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    (view : Env Γ ≃ Locals)
    (stateRel : Model → Locals → Heap → Prop) (test : Model → Bool) (next : Model → Model)
    (guardSpec : ∀ model,
      Stmt.BlockSpec (fun locals => Stmt.observe view guard program locals) (stateRel model)
        (fun _ _ _ _ => False)
        (fun _ _ again output finish => again = test model ∧ stateRel model output finish))
    (bodySpec : ∀ model, test model = true →
      Stmt.BlockSpec (fun locals => Stmt.observe view body program locals) (stateRel model)
        (fun _ _ output finish => stateRel (next model) output finish)
        (fun _ _ _ _ _ => False))
    (invariant : Model → Heap → Nat → Prop)
    (guardMeasured : ∀ model locals heap start, invariant model heap start →
      stateRel model locals heap →
      ArenaMeasured program w heapLimit depth guard
        (fun after _ finalCursor _ =>
          stateRel model (view after.locals) after.heap → invariant model after.heap finalCursor)
        ⟨view.symm locals, heap⟩ start)
    (bodyMeasured : ∀ model locals heap start, invariant model heap start →
      test model = true → stateRel model locals heap →
      ArenaMeasured program w heapLimit depth body
        (fun after _ finalCursor _ => stateRel (next model) (view after.locals) after.heap →
          invariant (next model) after.heap finalCursor)
        ⟨view.symm locals, heap⟩ start)
    {model : Model} {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program (.while guard body) entry finish control)
    (represented : stateRel model (view entry.locals) entry.heap)
    (initial : invariant model entry.heap cursor)
    (successful : control.Satisfies (fun _ => True) (fun _ _ => True) finish) :
    ∃ finalCursor, ArenaReady execution w heapLimit depth cursor finalCursor ∧
      control = .normal ∧ ∃ finalModel,
        stateRel finalModel (view finish.locals) finish.heap ∧
        invariant finalModel finish.heap finalCursor ∧ test finalModel = false := by
  apply while_model_of_exec view stateRel test next guardSpec bodySpec invariant
    (execution := execution) (represented := represented) (initial := initial)
    (successful := successful)
  · intro model current start valid related after decision tested observed
    have measured := guardMeasured model (view current.locals) current.heap start valid related
    simp only [Equiv.symm_apply_apply] at measured
    obtain ⟨finalCursor, _, ready, _, preserved⟩ :=
      measured.at_exec tested
    exact ⟨finalCursor, ready, preserved observed⟩
  · intro model current start valid active related after iterated observed
    have measured := bodyMeasured model (view current.locals) current.heap start valid active related
    simp only [Equiv.symm_apply_apply] at measured
    obtain ⟨finalCursor, _, ready, _, preserved⟩ :=
      measured.at_exec iterated
    exact ⟨finalCursor, ready, preserved observed⟩

end Ram.LanguageCompiler.ArenaReady
