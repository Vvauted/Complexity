/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured

/-!
# Calling existing measured arena executions

A returning `ArenaMeasured` supplies the actual callee execution, readiness and
core count directly to the existing call rule. Its final state, cursor and
observations pass to the continuation; the caller need not unpack witnesses.
Imports use the same proved relocation as exact calls.

An independent source specification can enrich the observations of that same
measured execution. It neither chooses another execution nor changes its count.
-/

namespace Ram.LanguageCompiler.ArenaMeasured

open Complexity.Language

/-- Call an existing measured body at its actual arguments and arena cursor.
The continuation receives its final state, retained observations and returned-value range;
the existing call rule adds body initialization and call overhead exactly once. -/
theorem call_measured
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {signature : Signature}
    (same : signatures[fn] = signature)
    {w heapLimit depth cursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt signatures (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {P : Complexity.Language.State signature.params → Value signature.result → Nat → Nat → Prop}
    (arguments : EnvFits w (args.eval entry.locals))
    (measured : ArenaMeasured program w heapLimit depth
      (cast (congrArg (fun s => Complexity.Language.Stmt signatures s.params s.result) same)
        (program.body fn))
      (fun finish control finalCursor coreSteps =>
        ∃ value, control = .returned value ∧ P finish value finalCursor coreSteps)
      (entry.enter (args.eval entry.locals)) cursor)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ∀ finish value calleeCursor coreSteps,
      P finish value calleeCursor coreSteps → ValueFits w value →
      ArenaMeasured program w heapLimit (depth + 1) continuation
        (fun finish control finalCursor tailSteps =>
          post finish.tail control finalCursor (callCost program fn (coreSteps + 2) + tailSteps))
        (Complexity.Language.State.cons value (entry.restore finish)) calleeCursor) :
    ArenaMeasured program w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq fn same args continuation) post entry cursor := by
  obtain ⟨finish, value, calleeCursor, coreSteps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  exact call_exact same (args := args) (entry := entry) (continuation := continuation)
    (callee := execution) (calleeReady := ready) arguments cost
    (body finish value calleeCursor coreSteps observed ready.outcome_fits)

/-- A measured imported body retains its source observations, actual final heap
and cursor. Only the enclosing call overhead uses the target function table. -/
theorem call_measured_imported
    {source target : List Signature}
    {sourceProgram : Complexity.Language.Program source}
    {targetProgram : Complexity.Language.Program target} {map : SignatureMap source target}
    (embedded : sourceProgram.Embeds map targetProgram)
    {fn : Fin source.length} {signature : Signature}
    (same : source[fn] = signature)
    {w heapLimit depth cursor : Nat} {Γ : List Ty} {result : Ty}
    {args : Args Γ signature.params}
    {continuation : Complexity.Language.Stmt target (signature.result :: Γ) result}
    {entry : Complexity.Language.State Γ}
    {P : Complexity.Language.State signature.params → Value signature.result → Nat → Nat → Prop}
    (arguments : EnvFits w (args.eval entry.locals))
    (measured : ArenaMeasured sourceProgram w heapLimit depth
      (cast (congrArg (fun s => Complexity.Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn))
      (fun finish control finalCursor coreSteps =>
        ∃ value, control = .returned value ∧ P finish value finalCursor coreSteps)
      (entry.enter (args.eval entry.locals)) cursor)
    {post : Complexity.Language.State Γ → Control result → Nat → Nat → Prop}
    (body : ∀ finish value calleeCursor coreSteps,
      P finish value calleeCursor coreSteps → ValueFits w value →
      ArenaMeasured targetProgram w heapLimit (depth + 1) continuation
        (fun finish control finalCursor tailSteps => post finish.tail control finalCursor
          (callCost targetProgram (map.toFun fn) (coreSteps + 2) + tailSteps))
        (Complexity.Language.State.cons value (entry.restore finish)) calleeCursor) :
    ArenaMeasured targetProgram w heapLimit (depth + 1)
      (Complexity.Language.Stmt.callOfEq (map.toFun fn)
        ((map.signature_eq fn).trans same) args continuation) post entry cursor := by
  obtain ⟨finish, value, calleeCursor, coreSteps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  exact call_exact_imported embedded same (args := args) (entry := entry)
    (continuation := continuation) (callee := execution) (calleeReady := ready) arguments cost
    (body finish value calleeCursor coreSteps observed ready.outcome_fits)

/-- Enrich the same measured function body with its independent mathematical
specification. The retained heap, returned value, cursor and core count are
unchanged; the source postcondition is applied to the already supplied execution. -/
theorem with_spec
    {signatures : List Signature} {program : Complexity.Language.Program signatures}
    {fn : Fin signatures.length} {w heapLimit depth cursor : Nat}
    {args : Env signatures[fn].params} {heap : Heap}
    {P : Complexity.Language.State signatures[fn].params →
      Value signatures[fn].result → Nat → Nat → Prop}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (measured : ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor coreSteps =>
        ∃ value, control = .returned value ∧ P finish value finalCursor coreSteps)
      ⟨args, heap⟩ cursor)
    (specification : FunctionTotal program fn pre post)
    (input : pre args heap) :
    ArenaMeasured program w heapLimit depth (program.body fn)
      (fun finish control finalCursor coreSteps =>
        ∃ value, control = .returned value ∧
          (P finish value finalCursor coreSteps ∧ post args heap value finish.heap))
      ⟨args, heap⟩ cursor := by
  obtain ⟨finish, value, finalCursor, coreSteps, execution, ready, cost, observed⟩ :=
    exists_returned_iff.mp measured
  exact exists_returned_iff.mpr
    ⟨finish, value, finalCursor, coreSteps, execution, ready, cost, observed,
      specification.postcondition (args := args) (heap := heap) input execution⟩

end Ram.LanguageCompiler.ArenaMeasured
