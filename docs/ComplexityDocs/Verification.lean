/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

/-!
# Proving correctness

Start with the mathematical result you want, then connect it to the implementation.
The correctness interface includes safety and termination, but asks for no time budget.
A separate [complexity proof](##ComplexityDocs.Complexity) can reuse the same invariants.

## Choose a specification

For source-facing proofs, start with `Ram.Source.TypedFunctionContract`. Its precondition
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
[getting started](##ComplexityDocs.GettingStarted) and the existing `square_contract`:

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
the underlying `apply_eq_of_execution` identifies raw fields.
`runTotal_correct_of_execution` also retains the source-visible final-state observation.
Neither normal halt nor projecting a result asserts that the body has no effects.

`Ram.LocalCompiler.Function.applyStateTyped_eq_of_execution` identifies the typed pair
with `(value, finish)`, while `applyStateTyped_spec` transfers a typed contract's
postcondition directly. The [typed runtime bridge](##Complexity.Computability.Ram.Compiler.Local.Function.Typed)
uses the same compiled run and does not introduce another runner.
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

## Use mathematical theorems at the interface

Once you have a refinement, prove properties of `f` using ordinary Lean and mathlib.
`Ram.Source.Refines.spec` transfers a theorem about `f x` to the implemented result.
`Ram.Source.Refines.with_postcondition` retains the property in the representation for
subsequent composition.

Reuse an operation's existing contract before unfolding its body. In particular:

- `Ram.Source.Refines.seq` composes two refinements through their shared intermediate model.
- `Ram.Source.Refines.congr_fun` changes the model by a proved equality of functions.
- `Ram.Source.Refines.equiv` changes mathematical coordinates through an equivalence.
- `Ram.Source.Refines.transfer` handles related, possibly lossy models when the functions
  respect the chosen relations.

The [graph-degree sample](##Examples.Ram.GraphDegree) is a concrete use of this boundary.
Its implemented operation is the [reusable array sum](##Complexity.Computability.Ram.Array.Sum).
The graph proof only identifies the represented row's list sum with mathlib's
`SimpleGraph.degree` and applies the existing function contract. It does not reprove
the traversal, register updates or unchanged-memory facts. The row is explicitly
preloaded; converting an abstract graph to that layout would need its own implementation.
Its `sum_eq_degree` theorem also states a direct equality about the ordinary executable
`ArraySum.sum`. It rewrites `ArraySum.sum_eq` and the mathematical adjacency-row sum,
without opening an execution relation or a calling-convention proof.

The array-sum source accepts `xs : array`, and `sumPair(left : array, right : array)`
calls it as `call sum(left)` and `call sum(right)`. The generated argument builders take
`Ram.ArrayRef` values; `array.Rep heapLimit xs entry` supplies the mathematical contents,
exact length and existing memory representation. `sum_function_contract_of_ref` and
`sumPair_function_contract` expose the returned list sums and unchanged shared state.
The two read-only references may overlap: this client does not need a disjointness premise.
Mutating operations still need their own aliasing and frame conditions. Passing a reference
does not prove its representation or execute a list loader. The
[array-argument sample](##Examples.Ram.ArrayArguments) uses
`sumFunctions.eval.sumPair left right heapLimit entry` for the mathematical result and
`sumFunctions.run.sumPair left right heapLimit entry` for actual compiled execution.
Its explicit heap and stack premises are separate from any time estimate; the
mathematical list concatenation does not allocate a new runtime array.

The [local-slice client](##Examples.Ram.ArraySlice) binds
`let window ← call slice(xs, offset, count);` and calls the imported sum on
the returned array reference. `slice` declares `: array` and returns
`subslice(xs, offset, count)`. `Ram.ArrayRef.Rep.subslice` supplies the ordinary
`(xs.drop offset.toNat).take count.toNat` representation;
`Ram.ArrayRef.Rep.subslice_end_lt` carries the parent's strict endpoint bound to
the selected interval. The slice contract carries the returned reference's representation
to the sum call, which reuses sum's existing contract rather than its traversal proof.
Descriptor evaluation and both returned fields are part of the compiled call, not
a host-side loader or copy. Containment, representation
and non-wrapping addresses remain explicit, and the postcondition preserves the
entire caller state, including arbitrary initial stream contents.

After `sumSlice_eq` identifies the ordinary executable result, the
[slice-properties client](##Examples.Ram.ArraySliceProperties) proves
`sumSlice_zero`, `sumSlice_whole` and `sumSlice_partition` by ordinary list reasoning.
The whole-slice result agrees with `ArraySum.sum`; the partition result adds the two
slice results modulo the word range. These proofs use the value equations and
standard `List.take`/`List.drop` identities, not execution relations, register updates
or loop proofs. The partition theorem compares returned values and does not compile
its two host applications into one program or supply their combined cost.

For a scoped `for` with one scalar expression update,
[the source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Expression)
`Ram.Source.Array.ForIn.Expression.function_contract` uses the generated body and
return equations to infer the private slots. Sum and count share its cursor progress,
termination and framing proof. The first argument is an array; additional word
parameters are retained automatically as the full `array.args ++ captures` prefix.
Count therefore needs no separate invariant to preserve its target.
The client still proves the actual expression's read safety and evaluation as the
mathematical fold step, using the supplied parameter equalities where needed.
Array representation, address range and the ordinary `List.foldl` identity also
remain mathematical obligations. The separate measured rule derives iteration
costs from compiled instructions; a host-language callback is not a free operation.
The [count client](##Examples.Ram.ArrayCount) then derives permutation invariance
directly from `List.Perm.count_eq`. It uses the typed reference contract for
`count(xs : array, target)`, with independently represented arrays that may live in
different heaps. The theorem equates returned counts, not the states or the work needed
to construct those arrays. Its `runCount_eq` theorem also covers an actual compiled
call with the target word as a runtime argument, returning the count independently
of stream output. The [sum client](##Examples.Ram.ArraySum) likewise reuses the function
contract and measured execution for its value equation and runner, without another
raw loop proof. Its ordinary `sum` application takes representation/range evidence
and a stack-capacity proof, both erased at runtime; `sum_eq` identifies the actual
returned natural number. No mathematical list is passed as executable data.
Fixed verified helper calls have their own
[source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Function);
richer bodies, multiple accumulators, mutation and short-circuiting still need
further proof interfaces.

These rules operate on fixed source statements. They do not turn an arbitrary mathematical
function into executable code. See [data models](##ComplexityDocs.Models) for array, matrix,
partial-map and framing interfaces.

## Loops and recursive calls

For a loop, choose a mathematical invariant and a well-founded progress argument.
`Ram.Source.Refines.while_wellFounded` relates the real guard and body to an abstract step
and eventual result. If a decreasing natural number is enough,
`Ram.Source.Verification.TotalWP.while_variant` provides a direct total-correctness rule.
The guard, representation and safety obligations remain at the implementation boundary.

For a callable recursive function, ordinary mathematical induction can prove
`Ram.Source.FunctionContract` directly. The [factorial example](##Examples.Ram.Factorial)
uses natural-number induction in `function_contract`: `ram_total_vc args entry rfl`
starts the function proof from its generated body and return equations, and
`ram_total_apply` applies the induction hypothesis at the smaller argument.
This main correctness proof does not construct a `TotalSpec`, name local registers
or prove stack-frame equations. The mathematical induction, argument-range facts
and word-arithmetic lemmas remain explicit; no time budget enters the proof.

`Ram.Source.Refines.call` can package a proved function specification as a refinement
of a call. Argument binding and return adaptation are handled at this boundary;
shared heap and I/O effects survive return, while the call theorem restores the
caller's other locals.

The API chapters on [control flow](##Complexity.Computability.Ram.Verification.Control),
[total recursion](##Complexity.Computability.Ram.Verification.Recursion.Total) and
[calls](##Complexity.Computability.Ram.Verification.Call) give the exact premises.

Use `Ram.Source.Recursion.TotalSpec` when the specification also needs the complete
callee-body endpoint. Its well-founded rules establish that stronger conclusion;
`Ram.Source.Recursion.TotalSpec.verify_wellFounded_function` presents smaller
invocations as argument/result contracts while retaining the body-state obligation.
The factorial example's separate `recursive_total` theorem instead unfolds one body
step and reuses `function_contract` to prove its local-state endpoint explicitly.
A returned value and restored caller state do not determine the callee's discarded
locals. This stronger interface is available when needed, not a prerequisite for
the function's main correctness proof. Neither route automatically chooses a
termination argument or compiles an arbitrary ordinary Lean definition.

## Stateful mathematical models

Use `StateM σ α` when a sequence of updates is easier to describe with state and a returned
value. It is an optional semantic model, not a second program every user must write.
Lean's `Std.Do.Triple` and `mvcgen` can prove its mathematical specification.
The same I/O example contains:

```lean
def incrementState : StateM (Word w) PUnit := do
  let value ← get
  set (value + 1)

open Std.Do in
theorem incrementState_spec (x : Word w) :
    ⦃fun state => ⌜state = x⌝⦄ incrementState
    ⦃⇓ _ state => ⌜state = x + 1⌝⦄ := by
  mvcgen [incrementState]
  simp_all
```

`Ram.Source.Refines.stateM_spec` transfers such a triple through a proved refinement of
`model.run`. `Ram.Source.Refines.stateM_spec_refines` keeps the native postcondition for
later operations. `Ram.Source.Refines.stateM_bind` composes returned values and state;
its mathematical continuation may depend on a returned value, but the corresponding source
statement is fixed and must obtain that value through its representation.

There are also [call](##Complexity.Computability.Ram.Verification.StateM.Call) and
[finite traversal](##Complexity.Computability.Ram.Verification.StateM.Traversal) bridges.
The call bridge represents returned fields as an ordinary list. Its register-observation
form requires distinct destinations to recover every field from the final registers;
the source call itself permits repeated destinations with last-write-wins assignment.
`mvcgen` verifies the mathematical model: it does not compile arbitrary Lean code or discharge
the model-to-memory connection. Reuse an existing bridge where one is available.

## Automate the routine work

`ram_refine x s hs [facts]` starts a refinement proof;
`ram_total_vc s pattern [facts]` starts a state-based total-contract proof;
`ram_total_vc args entry pattern [facts]` starts a `FunctionContract` directly.
Precondition patterns include `rfl` and `⟨rfl, hbound⟩`. Closed frame bounds may
be discharged automatically; unresolved obligations remain ordinary Lean goals.
Use `ram_total_apply contract [facts]` to apply a supplied operation, function or
recursive specification while keeping its implementation opaque. The dedicated
`ram_bindings` set supplies declaration-generated argument fields, lookups and
static parameter/result/local counts, including imported functions. Authors
still choose the contract and typed input, but need not repeat caller/callee
argument-builder definitions. Bodies, return expressions and mathematical
representation lemmas are not registered in this set.
`ram_model [facts]` simplifies observations, and `ram_word [facts]` normalizes word arithmetic
with the available range conditions. Remaining obligations are ordinary Lean goals.

Supply representation equations and mathematical facts through these tactic arguments or
Lean's usual `simp` mechanism. The tactics do not infer loop invariants, invent no-overflow
hypotheses or turn modular arithmetic into exact arithmetic. Their API is under
[total verification](##Complexity.Tactic.Ram.Total) and
[model simplification](##Complexity.Tactic.Ram.Model).

## Reuse contracts for included functions

The [source-composition sample](##Examples.Ram.FunctionComposition) includes the
existing copy and sum declarations as `Copy` and `Sum`, then calls them inside one
new function. `functions.importMap.Copy` gives the old-to-new function index map;
`functions.embeds.Copy` proves that the relocated implementation belongs to the
combined table. The [function-linking rule](##Complexity.Computability.Ram.Source.Function.Linking)
`Ram.Source.FunctionContract.renameCalls` transports the original contract through
this embedding, retaining its arguments, returned value and shared-state postcondition.

Apply that contract with `ram_total_apply` and the generated
`functions.function_lookup.Copy.copy` fact, then reuse the sum contract through
`functions.embeds.Sum`. Copy's postcondition supplies the destination representation
needed by sum. `Copy.copy` really returns `Unit`, so the standalone
`call Copy.copy(...);` has an empty result list and no dummy destination.
Its postcondition and shared-memory effects still reach the continuation through
the same call rule. This differs from discarding a word or array result, whose
fields are still evaluated and received into private destinations.
Relocation does not discharge representation, equal-length or
disjointness premises. The proof composes the existing contracts without expanding
either callee loop; the generated `applyState` result belongs to one compiled run,
unlike the host-level sequencing in `ArrayCopyFunction`.

The same sample's `imported_sumPair_eval` transports the existing two-array execution
through `functions.embeds.Sum` to `functions.eval.Sum.sumPair`. This also exercises
relocation of the imported function's own two calls to sum, without reopening them
or their loops. Imported aliases export lookup, argument and all six observation/run
interfaces; body equations and local-register names remain with the original declaration.
Generated `params_eq` and `locals_eq` equations are also available under imported
aliases. They expose calling-convention sizes without unfolding the callee body.
The separate time proof reuses the same functional postcondition: `ram_time_apply`
passes copy's destination representation to the remaining sum-call bound. Its
`reserving` argument belongs only to that time proof, not this correctness contract
or the executable call. See [proving complexity](##ComplexityDocs.Complexity).

## Publish and link a verified implementation

Use `Ram.TotalComponent.ofNamed` to package a fixed named program with its
`Ram.Source.TotalContract`, shared input/output representations and safety capacities.
There is no time-bound field. `Ram.TotalComponent.comp` links independent function tables
and composes their total correctness on the actual intermediate representation.

Heap and call-depth capacities are still required for safety, and the output-size guarantee
supports later composition. These are not proposed instruction budgets.
`Ram.TotalComponent.runs_observed` exports an actual halted execution before time analysis.
See [budget-free components](##Complexity.Computability.Ram.Component.Total).

## Attach time and export the result

`Ram.Source.TimeBound` bounds completed measured executions; alone, it does not prove that
one exists. Combine it with the correctness proof using
`Ram.Source.TotalContract.with_timeBound` or `Ram.Source.Refines.with_timeBound`.
The resulting contract bounds the same safe terminating execution.

For a reusable program, establish a scalar, input-size-based time envelope through
`Ram.TotalComponent.TimeBoundOn`, then use `Ram.TotalComponent.withTimeBound` to obtain
a resource-aware `Ram.Component`. A bound depending on the full input can first be
majorized by such an envelope.
The generated code and non-time guarantees are unchanged; existing component certificates
and polynomial-time interfaces remain available.

Correctness can also be exported without a time estimate.
`Ram.Source.Refines.compile_observed` transports represented outputs to an actual halted
target execution; `Ram.Source.Refines.compile_observed_with_timeBound` adds the separate
time bound. Code fit, stack capacity and output-observation transport are explicit premises.
The [backend chapter](##ComplexityDocs.Backend) explains these premises and the extra
instructions counted at the whole-program boundary.
-/
