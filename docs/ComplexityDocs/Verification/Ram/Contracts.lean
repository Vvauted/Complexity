/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Ram.ArrayCopyFunction
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySum
import Examples.Ram.Factorial
import Examples.Ram.FactorialFunction
import Examples.Ram.FunctionRun
import Examples.Ram.LocalBindings
import Examples.Ram.Merge
import Examples.Ram.MergeSort
import Examples.Ram.Verification

/-!
# Direct word-RAM contracts and execution

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Choose a specification

For the existing word-RAM language, start with `Ram.Source.TypedFunctionContract`. Its precondition
describes typed arguments and caller state; its postcondition describes the declared
`Word w`, `ArrayRef w` or `Unit` result and shared-state effects. The argument encoder
and result kind reuse the [source-value representation](##Complexity.Computability.Ram.Source.Value).
`TypedFunctionContract.of_wp` proves a body directly, and `wp_call` gives the typed value
to the continuation. `of_raw` reuses an existing raw contract; `raw` connects a chosen typed
input to the existing independent time rules. These are views of the same implementation,
not new execution relations, and require neither a `main` nor a time budget. See
[typed function contracts](##Complexity.Computability.Ram.Verification.Function.Typed).

`Ram.Source.FunctionContract` remains the raw field-list interface used by existing
implementation proofs. Its precondition describes word arguments and caller state;
its postcondition describes returned fields and shared-state effects.
`Ram.Source.FunctionExec` defines those observations through the function's real body and
return expressions: the returned list is `f.results.map callee.eval`, with every field
evaluated in the same final callee state. Scalar, array and `Unit` returns have one,
two and zero fields respectively. A mathematical specification is a property of that execution,
not a replacement implementation.

The `input` and `outputRev` fields in `Ram.Source.State` are shared stream state, not the
function's arguments and return value. Only actual source `read` and `write` operations
consume or append stream words. Function contracts quantify over entry states satisfying
their precondition; they do not automatically assume empty streams or unchanged effects.
In the factorial contract, the precondition only restricts the argument list and the
postcondition says `finish = entry`. Thus `function_runs` proves termination and the
factorial result for arbitrary initial stream contents, while preserving those contents.
The optional `read`/call/`write` main is verified separately.
Choosing `Source.State.initial []` in a wrapper only chooses an entry state: it does
not add a read, supply function arguments through a stream or prove independence
from other entry states.

The [factorial example](##Examples.Ram.Factorial) returns a word and preserves caller state.
The [array-copy function](##Complexity.Computability.Ram.Array.Function) instead changes
represented arrays in shared memory. Its public contract hides parameter registers but
retains genuine address-range, length and non-overlap assumptions.
`Ram.Source.FunctionContract.wp_call` reuses a contract at another function's call site;
the continuation receives the returned fields, the proved postcondition and preserved caller locals.
The [local-binding sample](##Examples.Ram.LocalBindings) retains this raw interface and composes its call rule twice
through `ram_total_apply`. Its direct proof uses the source declaration from
[direct word-RAM guide](ComplexityDocs/GettingStarted/WordRam.html) and the existing
`square_contract`:

```lean
theorem squaredNorm_contract (heapLimit : Nat) (x y : Word w) :
    Source.FunctionContract functions.program heapLimit 1 functions.function.squaredNorm
      (fun args _ => args = functions.arguments.squaredNorm x y)
      (fun _ entry value finish => value = [x * x + y * y] ∧ finish = entry) := by
  ram_total_vc args entry rfl [functions.body_eq.squaredNorm, functions.result_eq.squaredNorm]
  ram_total_apply (square_contract heapLimit x) [functions.function_lookup.square]
  ram_total_apply (square_contract heapLimit y) [functions.function_lookup.square]
```

`ram_total_vc args entry pattern [facts]` starts the `FunctionContract` using
`Ram.Source.FunctionContract.of_wp`: declared arguments are bound, and the
postcondition observes the real return fields and shared state. The pattern
`rfl` here substitutes the specified argument list. Each `ram_total_apply` uses
the supplied function contract and lookup fact without unfolding `square`'s body.
Here simplification automatically substitutes the postcondition's equalities for
the returned value and final state into the continuation. No manual `rintro` or
final `rfl` is needed. Non-equational postconditions still leave ordinary continuation
goals. This proof needs no separate intermediate-state specification, register
arithmetic or stack layout.
Argument and result arities must match the callee signature. Unresolved arity, frame
and return-expression read-safety obligations remain explicit. `of_body` remains
useful when a body refinement or invariant is already available; the tactics do not
discover invariants or select reusable contracts automatically.
The sample's independent `squaredNorm_bodyTime` theorem identifies the same body's count
as 46. It includes both calls to `square`, not `squaredNorm`'s own final return expression
or its enclosing calling convention.

The same `ram_total_vc` supports `TypedFunctionContract` through its `of_wp` rule.
The [three-array merge](##Complexity.Computability.Ram.Array.Merge.Function) uses
`ram_total_vc` and `ram_total_apply` to call the already verified core: the remaining
goals are its three represented arrays and the post-call list representations.
It does not need another typed tactic or a second proof of the merge loop.

## Observe the implemented function

For a named declaration `p`, use `p.eval.f` for function-value equations and
`p.bodyTime.f` for separate body-count equations. These generated entry points take
the declared word or array parameters, then `heapLimit` and `entry`. They specialize
`Ram.Func.evalTyped` and `Ram.Func.bodyTime`, observing the same actual invocation through
mathlib's `Part`. The generated value interface decodes the declared field shape
to `Word w`, `ArrayRef w` or `Unit`, without a default for a missing field. Its equation has the form
`p.eval.f ... heapLimit entry = Part.some (value, finish)` and includes termination;
the typed result and shared state are both retained. The
[factorial function-value sample](##Examples.Ram.FactorialFunction) hides its canonical
entry state once and proves agreement with every actual caller state. Subsequent
mathematical propositions mention only its argument and observed value.
This is a noncomputable proof view, not executable ordinary Lean function syntax.
General stateful functions still depend on shared entry state, and insufficient heap
capacity can make an observation undefined.
The ordinary executable `p.apply.f` interface described below is separate;
it does not make these `Part` observations computable.

`TypedFunctionContract.eval_spec` transports the typed postcondition to this view;
`FunctionExec.evalTyped_eq_some` also transfers a concrete execution using the generated
`results_length` equation. Neither bridge asks clients to split result lists or reconstruct
an array reference from a specification.
`Ram.Source.FunctionContract.eval_spec` transports any postcondition to the raw field-list
view; the declared shape connects it to the generated typed view. The postcondition can
be a mathematical relation, not necessarily a reference algorithm.
`Ram.Source.FunctionContract.eval_with_timeBound` adds a separate bound to the same
invocation's `Ram.Func.bodyTime`. Neither observation is defined using the proposed
result property or time bound. Body time excludes this function's own final return
expressions and enclosing call overhead; it includes completed calls inside its body.

## Run the compiled function

To execute a declared function, use `p.run.f` with the same typed parameters,
`heapLimit` and `entry`, rather than the noncomputable `Part` observation.
It specializes `Ram.LocalCompiler.Function.runUntil` and returns
`Option (Ram.RunResult (Ram.State w))`, retaining machine state, actual steps and
stopping reason. It requires no instruction limit and does not discard effects.
The underlying `runUntil_of_execution` bridge derives a returned
machine result and its actual count from `FunctionExec`, with no proposed time budget.
Code and stack still have to fit the selected word width. To identify the count,
`runUntil_eq_of_execution` combines `FunctionExec` with a separately proved
`bodyTime = Part.some bodySteps` equation. The
[runnable factorial sample](##Examples.Ram.FunctionRun) uses this second bridge with
`FactorialFunction.bodyTime_eq` to identify the value and full count of the same
application used by `#eval`. General divergent programs do not
return a nontermination flag; use `Ram.LocalCompiler.Function.run` when an operational
limit is desired. Unlike body time, the complete run counts the outer call, return
and halt. The generated entry point does not prove capacity or construct represented arrays.

## Prove properties of an executable application

For an ordinary executable value, use `p.apply.f ... heapLimit entry h`; use
`p.applyState.f ... heapLimit entry h` for its typed result and reusable source shared state,
or `p.runTotal.f ... heapLimit entry h` for the complete machine result.
All three require `Ram.LocalCompiler.Function.Halts` for those exact arguments and
entry state: the actual `runUntil` equals `some result` and `result.reason = .halted`.
An `isSome` proof alone would also admit faults and is not enough for this interface.
The [total-call bridge](##Complexity.Computability.Ram.Compiler.Local.Function.Total)
`halts_of_execution` derives this fact from budget-free `FunctionExec` with the
compiled-code and stack premises. It does not require a cost theorem.
`halts_of_typedContract` takes an existing typed contract and its precondition;
`halts_of_contract` is the corresponding raw-contract rule. Both work
without making the client first extract a returned value and execution witness.

For these runtime bridges, use `ram_run_apply theorem [facts]` from
[runner proof automation](##Complexity.Tactic.Ram.Run). It applies the supplied theorem,
selects the same standard compiled call-and-halt code used by the runner, and checks
static compilation, lookup and code-fit obligations at that use site. Generated
declaration bindings and supplied facts are used only for those static goals;
unresolved goals remain explicit.
The [factorial](##Examples.Ram.FunctionRun), [sum](##Examples.Ram.ArraySum) and
[slice](##Examples.Ram.ArraySlice) clients use it for halt, value and separate step proofs
without maintaining private `rawLink`, compilation and code-length declarations.
Stack capacity, representation, overflow and the supplied correctness or time theorem
remain explicit proof obligations. This is proof automation, not another runtime wrapper
or a guarantee that every `ram_def` compiles and fits every word width.

For a complete invocation's upper bound, `ram_run_bound theorem [facts]` also
compares the bridge's proved bound with the requested one. It reuses `ram_bound`
to normalize actual argument, return, frame and halt overhead; supply the
generated return-expression equation where needed. The copy, slice and
source-composition consumers no longer hand-expand those instruction counts.
Unresolved stack and mathematical obligations remain visible, and the requested
bound is never passed to the runner as fuel.

`runTotal` performs `Option.get` on the actual runner output; generated `apply` decodes
its returned fields using the declared result shape. The proof argument is in `Prop`
and erased at runtime, not a supplied answer extracted from a specification.
Use `Ram.LocalCompiler.Function.applyTyped_eq_of_execution` for the generated typed value;
the underlying `apply_eq_of_execution` identifies raw fields. When starting with
a typed contract, prefer `Ram.LocalCompiler.Function.applyTyped_spec`: provide
its precondition and a mathematical implication from the postcondition to the
desired value property. The lower-bound and slice-sum equations use this rule
without unpacking an execution or reconstructing the returned fields.
`runTotal_correct_of_execution` also retains the source-visible final-state observation.
Neither normal halt nor projecting a result property asserts that the body has no effects.

`Ram.LocalCompiler.Function.applyStateTyped_eq_of_execution` identifies the typed pair
with `(value, finish)`, while `applyStateTyped_spec` transfers a typed contract's
postcondition directly. The [typed runtime bridge](##Complexity.Computability.Ram.Compiler.Local.Function.Typed)
uses the same compiled run and does not introduce another runner.
The [merge application](##Examples.Ram.Merge) uses `applyStateTyped_spec` directly:
`Function.merge_spec` describes its three arrays and preserved frame, and
`Function.merge_contents` rewrites the actual destination to standard `List.merge`.
The sorted-permutation corollary then uses existing list mathematics.
For recursive operations on two buffers, `ArrayAt.reassemble_prefix_of_frame_two`
and `reassemble_suffix_of_frame_two` combine a changed half with the preserved half
using the operation's actual two-buffer frame. These
[shared array rules](##Complexity.Computability.Ram.Array.TwoBuffer) already shorten
both recursive merge-sort stages without fixing registers, return values or
equal buffer sizes in the rules. Slice containment, disjointness and the changed
half's length remain explicit premises.
The [typed recursive declaration](##Complexity.Computability.Ram.Array.MergeSort.Function)
uses these rules through its [representation stages](##Complexity.Computability.Ram.Array.MergeSort.Stages).
Its correctness proof is ordinary induction on list length, generalizing over
the source and scratch references so that both actual recursive calls reuse
the same hypothesis. `TypedFunctionContract.renameCalls` transports imported
operations through the existing embedding; `mono_depth` increases a genuine
call-depth capacity without introducing a time budget.
The [executable client](##Examples.Ram.MergeSort) then states sortedness,
permutation and a contents-level `StateM` equality using existing list theorems.
Scratch may change and remains represented; those effects are not erased by
the mathematical contents projection. The typed correctness calls use
`TypedFunctionContract.wp_call_restored`: their continuation sees the actual
shared effects with caller bindings already restored, so subsequent calls need
no accumulated register-restoration equalities. Ordinary result assignment still
occurs. `FunctionTimeBound.call_seq_typed_restored_at` gives the separate time
proof the same restored-state interface; the default remaining-reserve variant
also removes hand-selected intermediate budgets. Mathematical representation and
whole-algorithm cost arguments remain explicit.
The raw `applyState_eq_of_execution` identifies `(values, finish)`.
Its `returnState` projection keeps entry registers, takes actual target memory below
`heapLimit` and entry memory outside it, and retains actual input/output effects.
Safe execution preserves out-of-heap source memory, so this recovers the entire
source final state without equating it with the target's private stack.
`applyState_spec` transfers any existing `FunctionContract` postcondition to that
pair, with the contract's precondition and the compilation/capacity premises.
The [copy client](##Examples.Ram.ArrayCopyFunction) decodes its zero fields as `Unit`
and uses this rule for its destination contents, frame and stream-preservation claims,
then reuses them to call sum on the
returned state; it does not reopen the copy loop.

The [factorial application](##Examples.Ram.FunctionRun) proves ordinary equations
`factorial_eq_mod` and `factorial_eq`, and positivity using mathlib, about its
executable `factorial n hstack : Nat`. The latter two retain the no-overflow premise.
These values can be executed with `#eval`; their mathematical equalities use the
proved execution bridge, not kernel computation by `rfl`. The underlying word width,
capacity and entry-state restrictions are not removed by an ordinary return type.

## State and refinement specifications

Use `Ram.Source.TotalContract` when the precondition and postcondition directly describe
the source state. `Ram.Source.TotalRelContract` also lets the postcondition refer to the
entry state, which is useful for framing unchanged data.

Use `Ram.Source.Refines` when an ordinary Lean function is the clearest description of the
result. Its arguments have the following shape:

```lean
Refines program heapLimit depth stmt inputRep outputRep f
```

For every mathematical input `x`, an entry state satisfying `inputRep x` safely terminates
in a state satisfying `outputRep (f x)`. The predicates connect words and memory to the
mathematical values; they may also carry encoding, capacity and frame assumptions.
They do not require a bijection between an entire heap and a value.

Here is the refinement proof from [the small I/O example](##Examples.Ram.Verification).
Its `main` reads a word, increments it, and writes the result:

```lean
theorem main_refines (rest out : List (Word w)) :
    Refines [] 0 0 main
      (fun x s => s.input = x :: rest ∧ s.outputRev = out)
      (fun y t => t.input = rest ∧ t.outputRev = y :: out)
      (fun x : Word w => x + 1) := by
  ram_refine x s ⟨hin, hout⟩ [main, increment, hin, hout]
```

This is modular word addition. The proof also retains the input tail and prior output;
it does not silently reinterpret the computation as unbounded natural-number addition.
-/
