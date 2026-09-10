/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization

/-!
# Function admissibility for allocation-aware compilation

`FunctionArenaRealizable` packages word ranges, call nesting and arena capacity
for a real returned source invocation. Its admissibility predicate includes the
entry cursor, so the same function can be used again after preceding allocations.
There are no registers, physical placements, execution budgets or target runs in
this interface. Their separate compiler theorems consume the resulting readiness.

Independent source total correctness supplies mathematical behavior and can
supply termination to a conditional readiness proof. Determinism transfers
readiness to the exact source execution selected by that correctness proof.
Existing nonallocating realization proofs remain usable with an unchanged cursor.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Source-level conditions suffice for a returned invocation whose actual
operations fit the selected word, nesting and allocation capacities. -/
def FunctionArenaRealizable {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (w heapLimit depth : Nat)
    (fn : Fin signatures.length)
    (pre : Env signatures[fn].params → Heap → Nat → Prop) : Prop :=
  ∀ args heap cursor, pre args heap cursor →
    ∃ finish value finalCursor,
      ∃ execution : Complexity.Language.Exec program (program.body fn)
        ⟨args, heap⟩ finish (.returned value),
        ArenaReady execution w heapLimit depth cursor finalCursor

namespace FunctionArenaRealizable

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {w heapLimit depth : Nat} {fn : Fin signatures.length}
variable {feasible feasible' : Env signatures[fn].params → Heap → Nat → Prop}
variable {pre : Env signatures[fn].params → Heap → Prop}
variable {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}

/-- Strengthening the source-level admissibility condition preserves readiness. -/
theorem consequence
    (realizable : FunctionArenaRealizable program w heapLimit depth fn feasible)
    (input : ∀ args heap cursor, feasible' args heap cursor → feasible args heap cursor) :
    FunctionArenaRealizable program w heapLimit depth fn feasible' :=
  fun args heap cursor hpre => realizable args heap cursor (input args heap cursor hpre)

/-- Any independently supplied successful execution of the same invocation has
the readiness of the resource witness, with its actual final heap and value. -/
theorem ready_of_exec
    (realizable : FunctionArenaRealizable program w heapLimit depth fn feasible)
    {args : Env signatures[fn].params} {heap : Heap} {cursor : Nat}
    {finish : Complexity.Language.State signatures[fn].params}
    {value : Value signatures[fn].result}
    (hfeasible : feasible args heap cursor)
    (execution : Complexity.Language.Exec program (program.body fn)
      ⟨args, heap⟩ finish (.returned value)) :
    ∃ finalCursor, ArenaReady execution w heapLimit depth cursor finalCursor := by
  obtain ⟨otherFinish, otherValue, finalCursor, otherExec, ready⟩ :=
    realizable args heap cursor hfeasible
  obtain ⟨rfl, sameControl⟩ := otherExec.deterministic execution
  cases Control.returned.inj sameControl
  exact ⟨finalCursor, ready⟩

/-- Mathematical total correctness supplies termination; the separate resource
proof needs to establish only readiness conditional on a returned execution. -/
theorem of_functionTotal
    (specification : FunctionTotal program fn pre post)
    (input : ∀ args heap cursor, feasible args heap cursor → pre args heap)
    (resources : ∀ args heap cursor, feasible args heap cursor →
      ∀ finish value,
        ∀ execution : Complexity.Language.Exec program (program.body fn)
          ⟨args, heap⟩ finish (.returned value),
          ∃ finalCursor, ArenaReady execution w heapLimit depth cursor finalCursor) :
    FunctionArenaRealizable program w heapLimit depth fn feasible := by
  intro args heap cursor hfeasible
  obtain ⟨finish, value, execution, _⟩ :=
    specification args heap (input args heap cursor hfeasible)
  obtain ⟨finalCursor, ready⟩ := resources args heap cursor hfeasible finish value execution
  exact ⟨finish, value, finalCursor, execution, ready⟩

/-- Attach the resource witness to the exact returned execution selected by an
independent source contract. Correctness and feasibility retain separate inputs. -/
theorem with_specification
    (realizable : FunctionArenaRealizable program w heapLimit depth fn feasible)
    (specification : FunctionTotal program fn pre post)
    (args : Env signatures[fn].params) (heap : Heap) (cursor : Nat)
    (hfeasible : feasible args heap cursor) (hpre : pre args heap) :
    ∃ finish value finalCursor,
      ∃ execution : Complexity.Language.Exec program (program.body fn)
        ⟨args, heap⟩ finish (.returned value),
        ArenaReady execution w heapLimit depth cursor finalCursor ∧
          post args heap value finish.heap := by
  obtain ⟨finish, value, execution, property⟩ := specification args heap hpre
  obtain ⟨finalCursor, ready⟩ := realizable.ready_of_exec hfeasible execution
  exact ⟨finish, value, finalCursor, execution, ready, property⟩

end FunctionArenaRealizable

namespace FunctionRealizable

/-- Existing fixed-placement range proofs embed without new capacity or cursor
obligations: these executions perform no allocations and retain the entry cursor. -/
theorem arenaRealizable {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {fn : Fin signatures.length} {pre : Env signatures[fn].params → Heap → Prop}
    (realizable : FunctionRealizable program w depth fn pre) (heapLimit : Nat) :
    FunctionArenaRealizable program w heapLimit depth fn (fun args heap _ => pre args heap) := by
  intro args heap cursor hpre
  obtain ⟨finish, value, execution⟩ := realizable args heap hpre
  exact ⟨finish, value, cursor, execution.erase, execution.arenaReady heapLimit cursor⟩

end FunctionRealizable
end Ram.LanguageCompiler
