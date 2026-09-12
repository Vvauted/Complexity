/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources
import Complexity.Language.Linking.Verification

/-!
# Composing calls with shared-heap resource contracts

Returning calls retain the callee's actual heap and arena cursor. The continuation
runs at the caller's depth, so sequential calls reuse that depth rather than adding
their depths. Complete-signature transport permits arbitrary typed arguments.

`ArenaExecutionCost.call_measuredOfEq` composes existing exact observations. Its
postcondition retains the continuation's count, including exact counts and cursor
equations supplied by a client. `FunctionArenaResources.call_measuredOfEq` first
uses an independent source total-correctness contract and the callee's existing
resource and cost contracts. It then applies the same exact rule and transports
the bound through the compiler-derived call overhead.

These rules introduce neither execution semantics nor a cost model. They charge
callee body initialization once; the enclosing function's own initialization and
outer invocation remain the enclosing caller's responsibility.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- Compose an exactly measured callee with its actual continuation. The final
property can retain the continuation's exact count as well as its heap and cursor.
The continuation and the whole call have the same available call depth. -/
theorem ArenaExecutionCost.call_measuredOfEq
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {w heapLimit depth cursor calleeCursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params}
    {value : Value signature.result}
    {callee : Complexity.Language.Exec program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {calleeReady : ArenaReady callee w heapLimit depth cursor calleeCursor}
    {calleeSteps : Nat}
    (arguments : EnvFits w (args.eval entry.locals))
    (calleeCost : ArenaExecutionCost calleeReady calleeSteps)
    {property : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ∃ finish control finalCursor tailSteps,
      ∃ execution : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) calleeCursor finalCursor,
        ArenaExecutionCost ready tailSteps ∧ property finish.tail control finalCursor tailSteps) :
    ∃ finish control finalCursor tailSteps,
      ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.Stmt.callOfEq fn same args continuation) entry finish control,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready (callCost program fn (calleeSteps + 2) + tailSteps) ∧
          property finish control finalCursor tailSteps := by
  obtain ⟨finish, control, finalCursor, tailSteps, execution, ready, cost, outcome⟩ := body
  refine ⟨finish.tail, control, finalCursor, tailSteps,
    Complexity.Language.Exec.callReturnOfEq same callee execution,
    ArenaReady.callReturnOfEq same arguments calleeReady ready, ?_, outcome⟩
  exact ArenaExecutionCost.callReturnOfEq same (arguments := arguments) calleeCost cost

/-- Invoke an independently specified function and continue from its actual heap
and cursor. The mathematical index supplies arguments and budgets without choosing
a canonical heap representation. The continuation bound is fixed for this invocation
but may depend on any of its mathematical inputs. Its proof receives the actual
returned value, heap, range and retained-cursor bound.

The resulting bound includes the actual call frame and callee initialization;
the continuation's cost is charged at the same caller depth. -/
theorem FunctionArenaResources.call_measuredOfEq
    {X : Type u} {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {calleeArgs : X → Env signature.params} {resourcePre : X → Heap → Prop}
    {sourcePre : Env signature.params → Heap → Prop}
    {sourcePost : Env signature.params → Heap → Value signature.result → Heap → Prop}
    {w heapLimit depth : Nat} {reserve bound : X → Nat}
    (total : FunctionTotal program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) sourcePre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm) sourcePost))
    (resources : FunctionArenaResources program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs resourcePre w heapLimit depth reserve)
    (bounded : FunctionArenaCostBound program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn)) calleeArgs resourcePre w heapLimit depth bound)
    {Γ : List Ty} {result : Ty} {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ} {cursor tailBudget : Nat}
    (x : X) (arguments_eq : calleeArgs x = args.eval entry.locals)
    (allowed : resourcePre x entry.heap)
    (sourceAllowed : sourcePre (args.eval entry.locals) entry.heap)
    (arguments : EnvFits w (args.eval entry.locals))
    (capacity : cursor + reserve x ≤ heapLimit)
    {property : Complexity.Language.State Γ → Control result → Nat → Prop}
    (body : ∀ value heap calleeCursor,
      sourcePost (args.eval entry.locals) entry.heap value heap →
      ValueFits w value → calleeCursor ≤ cursor + reserve x →
      ∃ finish control finalCursor tailSteps,
        ∃ execution : Complexity.Language.Exec program continuation
          (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) finish control,
        ∃ ready : ArenaReady execution w heapLimit (depth + 1) calleeCursor finalCursor,
          ArenaExecutionCost ready tailSteps ∧ tailSteps ≤ tailBudget ∧
            property finish.tail control finalCursor) :
    ∃ finish control finalCursor steps,
      ∃ execution : Complexity.Language.Exec program
        (Complexity.Language.Stmt.callOfEq fn same args continuation) entry finish control,
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor finalCursor,
        ArenaExecutionCost ready steps ∧
          steps ≤ callCost program fn (bound x) + tailBudget ∧
          property finish control finalCursor := by
  obtain ⟨calleeFinish, value, callee, returned⟩ :=
    (FunctionTotal.cast_iff program fn same sourcePre sourcePost).mp total
      (args.eval entry.locals) entry.heap sourceAllowed
  have resourcesHere := resources x entry.heap cursor allowed
  have boundedHere := bounded x entry.heap allowed
  rw [arguments_eq] at resourcesHere boundedHere
  obtain ⟨calleeCursor, calleeReady, cursorBound⟩ :=
    resourcesHere arguments capacity calleeFinish value callee
  obtain ⟨calleeSteps, calleeCost⟩ := calleeReady.exists_cost
  have calleeBound := boundedHere calleeFinish value callee calleeReady calleeCost
  have valueFits : ValueFits w value := calleeReady.outcome_fits
  obtain ⟨finish, control, finalCursor, tailSteps, execution, ready, cost,
      tailBound, outcome⟩ :=
    ArenaExecutionCost.call_measuredOfEq same arguments calleeCost
      (property := fun finish control finalCursor tailSteps =>
        tailSteps ≤ tailBudget ∧ property finish control finalCursor)
      (body value calleeFinish.heap calleeCursor returned valueFits cursorBound)
  refine ⟨finish, control, finalCursor, _, execution, ready, cost, ?_, outcome⟩
  exact Nat.add_le_add (callCost_mono program fn calleeBound) tailBound

end Ram.LanguageCompiler
