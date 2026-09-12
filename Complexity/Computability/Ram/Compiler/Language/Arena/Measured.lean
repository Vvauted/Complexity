/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.FunctionResources.Call

/-!
# Structural composition of measured source executions

`ArenaMeasured` is a proposition packaging an existing source execution, its
arena readiness and its actual compiler count. Its postcondition observes the
same final state, control, cursor and count. Equalities and upper bounds use the
same interface; there is no additional execution semantics or instruction price.

Calls resume at the actual callee heap and cursor. Callee contracts remain
independent source correctness, resource and cost proofs, and the continuation
receives the actual callee count together with its bound. Sequential calls reuse
the caller's available depth. Imported contracts are transported through a proved
embedding of the actual bodies, without unfolding their implementations.

Counts describe the current statement's core. Calling a function adds its two
body-initialization instructions exactly once; the enclosing function's own
initialization and outer invocation are still handled by the existing execution
theorem.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

universe u

/-- One existing source execution with its readiness, compiler count and final
observations. This only packages witnesses from the existing semantic relations. -/
def ArenaMeasured {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w heapLimit depth : Nat)
    {Γ : List Ty} {result : Ty} (stmt : Complexity.Language.Stmt signatures Γ result)
    (post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop)
    (entry : Complexity.Language.State Γ) (cursor : Nat) : Prop :=
  ∃ finish control finalCursor steps,
    ∃ execution : Complexity.Language.Exec program stmt entry finish control,
    ∃ ready : ArenaReady execution w heapLimit depth cursor finalCursor,
      ArenaExecutionCost ready steps ∧ post finish control finalCursor steps

namespace ArenaMeasured

/-- An empty statement preserves the actual state and cursor without instructions. -/
theorem skip {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (outcome : post entry .normal cursor 0) :
    ArenaMeasured program w heapLimit depth .skip post entry cursor := by
  exact ⟨entry, .normal, cursor, 0, Complexity.Language.Exec.skip entry,
    ArenaReady.skip entry, ArenaExecutionCost.skip entry, outcome⟩

/-- Assignment changes the selected source local, not the heap or arena cursor.
Its field encoding and copies use the existing primitive instruction count. -/
theorem assign {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {τ result : Ty} {target : Var Γ τ} {value : Prim Γ τ}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (fits : PrimFits w entry.locals value)
    (outcome : post (entry.set target (value.eval entry.locals)) .normal cursor
      (primCodeSize value)) :
    ArenaMeasured program w heapLimit depth (.assign target value) post entry cursor := by
  exact ⟨entry.set target (value.eval entry.locals), .normal, cursor, primCodeSize value,
    Complexity.Language.Exec.assign target value entry, ArenaReady.assign target value entry fits,
    ArenaExecutionCost.assign target value entry (fits := fits), outcome⟩

/-- Continue only after normal completion of the first statement, using its
actual state and cursor. Early return retains its existing short-circuit count
and never executes or charges the second statement. -/
theorem seq {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {first second : Complexity.Language.Stmt signatures Γ result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (head : ArenaMeasured program w heapLimit depth first
      (fun middle control middleCursor firstSteps => match control with
        | .normal => ArenaMeasured program w heapLimit depth second
            (fun finish control finalCursor secondSteps =>
              post finish control finalCursor (firstSteps + 2 + secondSteps)) middle middleCursor
        | .returned value => post middle (.returned value) middleCursor (firstSteps + 3)
        | .fault _ => False) entry cursor) :
    ArenaMeasured program w heapLimit depth (.seq first second) post entry cursor := by
  obtain ⟨middle, control, middleCursor, firstSteps, head, headReady, headCost, next⟩ := head
  cases control with
  | normal =>
      obtain ⟨finish, control, finalCursor, secondSteps, tail, tailReady, tailCost, outcome⟩ := next
      exact ⟨finish, control, finalCursor, firstSteps + 2 + secondSteps,
        Complexity.Language.Exec.seqNormal head tail, ArenaReady.seqNormal headReady tailReady,
        ArenaExecutionCost.seqNormal headCost tailCost, outcome⟩
  | returned value =>
      exact ⟨middle, .returned value, middleCursor, firstSteps + 3,
        Complexity.Language.Exec.seqReturn (second := second) head,
        ArenaReady.seqReturn (second := second) headReady,
        ArenaExecutionCost.seqReturn (second := second) headCost, next⟩
  | fault error => exact False.elim next

/-- The true branch retains its actual final observations and adds the existing
conditional control instructions, without executing or charging the false branch. -/
theorem iteTrue {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (selected : condition.eval entry.locals = true)
    (body : ArenaMeasured program w heapLimit depth yes
      (fun finish control finalCursor steps => post finish control finalCursor (steps + 3))
      entry cursor) :
    ArenaMeasured program w heapLimit depth (.ite condition yes no) post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish, control, finalCursor, steps + 3,
    Complexity.Language.Exec.iteTrue selected execution,
    ArenaReady.iteTrue (test := selected) ready,
    ArenaExecutionCost.iteTrue (test := selected) cost, outcome⟩

/-- The false branch uses its own actual heap, cursor and count. The existing
conditional lowering has a different short-circuit overhead on this path. -/
theorem iteFalse {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (selected : condition.eval entry.locals = false)
    (body : ArenaMeasured program w heapLimit depth no
      (fun finish control finalCursor steps => post finish control finalCursor (steps + 2))
      entry cursor) :
    ArenaMeasured program w heapLimit depth (.ite condition yes no) post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish, control, finalCursor, steps + 2,
    Complexity.Language.Exec.iteFalse selected execution,
    ArenaReady.iteFalse (test := selected) ready,
    ArenaExecutionCost.iteFalse (test := selected) cost, outcome⟩

/-- Split an unknown Boolean condition. Each proof obligation describes only
its selected branch; allocations and later continuations are not duplicated at runtime. -/
theorem ite {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (yesBranch : ∀ _selected : condition.eval entry.locals = true,
      ArenaMeasured program w heapLimit depth yes
        (fun finish control finalCursor steps => post finish control finalCursor (steps + 3))
        entry cursor)
    (noBranch : ∀ _selected : condition.eval entry.locals = false,
      ArenaMeasured program w heapLimit depth no
        (fun finish control finalCursor steps => post finish control finalCursor (steps + 2))
        entry cursor) :
    ArenaMeasured program w heapLimit depth (.ite condition yes no) post entry cursor := by
  cases selected : condition.eval entry.locals with
  | false => exact iteFalse selected (noBranch selected)
  | true => exact iteTrue selected (yesBranch selected)

/-- Change only the final observations, retaining the exact execution and count. -/
theorem mono_post {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {post post' : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (measured : ArenaMeasured program w heapLimit depth stmt post entry cursor)
    (implies : ∀ finish control finalCursor steps,
      post finish control finalCursor steps → post' finish control finalCursor steps) :
    ArenaMeasured program w heapLimit depth stmt post' entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := measured
  exact ⟨finish, control, finalCursor, steps, execution, ready, cost,
    implies finish control finalCursor steps outcome⟩

/-- A returned observation exposes the same returned execution directly, without
requiring a client to transport its readiness and cost through a control equality. -/
theorem exists_returned_iff {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {post : Complexity.Language.State Γ → Value result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat} :
    ArenaMeasured program w heapLimit depth stmt
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧ post finish value finalCursor steps) entry cursor ↔
      ∃ finish value finalCursor steps,
        ∃ execution : Complexity.Language.Exec program stmt entry finish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit depth cursor finalCursor,
          ArenaExecutionCost ready steps ∧ post finish value finalCursor steps := by
  constructor
  · rintro ⟨finish, control, finalCursor, steps, execution, ready, cost,
      value, rfl, outcome⟩
    exact ⟨finish, value, finalCursor, steps, execution, ready, cost, outcome⟩
  · rintro ⟨finish, value, finalCursor, steps, execution, ready, cost, outcome⟩
    exact ⟨finish, .returned value, finalCursor, steps, execution, ready, cost,
      value, rfl, outcome⟩

/-- Return the actual atom with the compiler's field-copy and return count. -/
theorem ret {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {result : Ty} {value : Atom Γ result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (fits : ValueFits w (value.eval entry.locals))
    (outcome : post entry (.returned (value.eval entry.locals)) cursor
      (2 * fieldCount result + 2)) :
    ArenaMeasured program w heapLimit depth (.ret value) post entry cursor := by
  exact ⟨entry, .returned (value.eval entry.locals), cursor, 2 * fieldCount result + 2,
    Complexity.Language.Exec.ret value entry, ArenaReady.ret value entry fits,
    ArenaExecutionCost.ret value entry (fits := fits), outcome⟩

/-- A primitive binding keeps the current heap and cursor; its actual emitted
work is added to the continuation's count in the final observation. -/
theorem letPrim {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth : Nat}
    {Γ : List Ty} {τ result : Ty} {value : Prim Γ τ}
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (fits : PrimFits w entry.locals value)
    (body : ArenaMeasured program w heapLimit depth continuation
      (fun finish control finalCursor steps =>
        post finish.tail control finalCursor (primCodeSize value + steps))
      (Complexity.Language.State.cons (value.eval entry.locals) entry) cursor) :
    ArenaMeasured program w heapLimit depth (.letPrim value continuation) post entry cursor := by
  obtain ⟨finish, control, finalCursor, steps, execution, ready, cost, outcome⟩ := body
  exact ⟨finish.tail, control, finalCursor, primCodeSize value + steps,
    Complexity.Language.Exec.letPrim execution, ArenaReady.letPrim fits ready,
    ArenaExecutionCost.letPrim (fits := fits) cost, outcome⟩

/-- Compose an existing exact callee observation with the actual continuation.
The final postcondition receives the complete current call count, not just the
continuation's count. The callee body initialization is included exactly once. -/
theorem call_exact
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {w heapLimit depth cursor calleeCursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params} {value : Value signature.result}
    {callee : Complexity.Language.Exec program
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {calleeReady : ArenaReady callee w heapLimit depth cursor calleeCursor}
    {calleeSteps : Nat}
    (arguments : EnvFits w (args.eval entry.locals))
    (calleeCost : ArenaExecutionCost calleeReady calleeSteps)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ArenaMeasured program w heapLimit (depth + 1) continuation
      (fun finish control finalCursor tailSteps =>
        post finish.tail control finalCursor (callCost program fn (calleeSteps + 2) + tailSteps))
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) calleeCursor) :
    ArenaMeasured program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) post entry cursor := by
  obtain ⟨finish, control, finalCursor, tailSteps, execution, ready, cost, outcome⟩ :=
    ArenaExecutionCost.call_measuredOfEq same (args := args) (entry := entry)
      (continuation := continuation) arguments calleeCost
      (property := fun finish control finalCursor tailSteps =>
        post finish control finalCursor (callCost program fn (calleeSteps + 2) + tailSteps)) body
  exact ⟨finish, control, finalCursor, _, execution, ready, cost, outcome⟩

/-- Reuse an exact callee observation through an actual program embedding.
Its source execution, heap effects, cursor and core count are unchanged; only
the enclosing call's overhead comes from the target function table. -/
theorem call_exact_imported
    {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {signature : Signature}
    (same : source[fn] = signature)
    {w heapLimit depth cursor calleeCursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt target (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {calleeFinish : Complexity.Language.State signature.params} {value : Value signature.result}
    {callee : Complexity.Language.Exec sourceProgram
      (cast (congrArg (fun s => Complexity.Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn))
      (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
    {calleeReady : ArenaReady callee w heapLimit depth cursor calleeCursor}
    {calleeSteps : Nat}
    (arguments : EnvFits w (args.eval entry.locals))
    (calleeCost : ArenaExecutionCost calleeReady calleeSteps)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ArenaMeasured targetProgram w heapLimit (depth + 1) continuation
      (fun finish control finalCursor tailSteps => post finish.tail control finalCursor
        (callCost targetProgram (map.toFun fn) (calleeSteps + 2) + tailSteps))
      (Complexity.Language.State.cons value (entry.restore calleeFinish)) calleeCursor) :
    ArenaMeasured targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn)
        ((map.signature_eq fn).trans same) args continuation) post entry cursor := by
  cases same
  obtain ⟨linked, linkedReady, linkedCost⟩ :
      ∃ execution : Complexity.Language.Exec targetProgram (map.body targetProgram fn)
          (entry.enter (args.eval entry.locals)) calleeFinish (.returned value),
        ∃ ready : ArenaReady execution w heapLimit depth cursor calleeCursor,
          ArenaExecutionCost ready calleeSteps := by
    rw [embedded fn]
    exact ⟨callee.renameCalls embedded, calleeReady.renameCalls embedded,
      calleeCost.renameCalls embedded⟩
  exact call_exact (map.signature_eq fn) arguments linkedCost body

/-- Independent callee contracts supply a real invocation. Its actual core count,
returned value, heap and cursor are passed to the continuation together with their
proved bounds. The postcondition may require exact facts, upper bounds or both. -/
theorem call_of_contract
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
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (x : X) (arguments_eq : calleeArgs x = args.eval entry.locals)
    (allowed : resourcePre x entry.heap)
    (sourceAllowed : sourcePre (args.eval entry.locals) entry.heap)
    (arguments : EnvFits w (args.eval entry.locals))
    (capacity : cursor + reserve x ≤ heapLimit)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ∀ value heap calleeCursor calleeCoreSteps,
      sourcePost (args.eval entry.locals) entry.heap value heap →
      ValueFits w value → calleeCursor ≤ cursor + reserve x →
      calleeCoreSteps + 2 ≤ bound x →
      ArenaMeasured program w heapLimit (depth + 1) continuation
        (fun finish control finalCursor tailSteps => post finish.tail control finalCursor
          (callCost program fn (calleeCoreSteps + 2) + tailSteps))
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) calleeCursor) :
    ArenaMeasured program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) post entry cursor := by
  obtain ⟨calleeFinish, value, callee, returned⟩ :=
    (FunctionTotal.cast_iff program fn same sourcePre sourcePost).mp total
      (args.eval entry.locals) entry.heap sourceAllowed
  have resourcesHere := resources x entry.heap cursor allowed
  have boundedHere := bounded x entry.heap allowed
  rw [arguments_eq] at resourcesHere boundedHere
  obtain ⟨calleeCursor, calleeReady, cursorBound⟩ :=
    resourcesHere arguments capacity calleeFinish value callee
  obtain ⟨calleeCoreSteps, calleeCost⟩ := calleeReady.exists_cost
  have coreBound := boundedHere calleeFinish value callee calleeReady calleeCost
  have valueFits : ValueFits w value := calleeReady.outcome_fits
  exact call_exact same arguments calleeCost
    (body value calleeFinish.heap calleeCursor calleeCoreSteps returned valueFits
      cursorBound coreBound)

/-- Use original callee contracts through an actual source-program embedding.
The continuation observes the mapped target function's real call overhead; clients
do not rewrite imported bodies or reconstruct signature casts themselves. -/
theorem call_of_contract_imported
    {X : Type u} {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {signature : Signature}
    (same : source[fn] = signature)
    {calleeArgs : X → Env signature.params} {resourcePre : X → Heap → Prop}
    {sourcePre : Env signature.params → Heap → Prop}
    {sourcePost : Env signature.params → Heap → Value signature.result → Heap → Prop}
    {w heapLimit depth : Nat} {reserve bound : X → Nat}
    (total : FunctionTotal sourceProgram fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) sourcePre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm) sourcePost))
    (resources : FunctionArenaResources sourceProgram
      (cast (congrArg (fun s => Complexity.Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn)) calleeArgs resourcePre w heapLimit depth reserve)
    (bounded : FunctionArenaCostBound sourceProgram
      (cast (congrArg (fun s => Complexity.Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn)) calleeArgs resourcePre w heapLimit depth bound)
    {Γ : List Ty} {result : Ty} {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt target (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ} {cursor : Nat}
    (x : X) (arguments_eq : calleeArgs x = args.eval entry.locals)
    (allowed : resourcePre x entry.heap)
    (sourceAllowed : sourcePre (args.eval entry.locals) entry.heap)
    (arguments : EnvFits w (args.eval entry.locals))
    (capacity : cursor + reserve x ≤ heapLimit)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ∀ value heap calleeCursor calleeCoreSteps,
      sourcePost (args.eval entry.locals) entry.heap value heap →
      ValueFits w value → calleeCursor ≤ cursor + reserve x →
      calleeCoreSteps + 2 ≤ bound x →
      ArenaMeasured targetProgram w heapLimit (depth + 1) continuation
        (fun finish control finalCursor tailSteps => post finish.tail control finalCursor
          (callCost targetProgram (map.toFun fn) (calleeCoreSteps + 2) + tailSteps))
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) calleeCursor) :
    ArenaMeasured targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn)
        ((map.signature_eq fn).trans same) args continuation) post entry cursor := by
  cases same
  change FunctionTotal sourceProgram fn sourcePre sourcePost at total
  change FunctionArenaResources sourceProgram (sourceProgram.body fn)
    calleeArgs resourcePre w heapLimit depth reserve at resources
  change FunctionArenaCostBound sourceProgram (sourceProgram.body fn)
    calleeArgs resourcePre w heapLimit depth bound at bounded
  have linkedTotal := FunctionTotal.renameCalls embedded total
  have linkedResources := resources.renameCalls embedded
  have linkedBounded := bounded.renameCalls embedded
  rw [← embedded fn] at linkedResources linkedBounded
  exact call_of_contract (map.signature_eq fn) linkedTotal linkedResources linkedBounded
    x arguments_eq allowed sourceAllowed arguments capacity body

end ArenaMeasured
end Ram.LanguageCompiler
