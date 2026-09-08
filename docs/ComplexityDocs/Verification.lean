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

For an intermediate function, start with `Ram.Source.FunctionContract`. Its precondition
describes arguments and caller state; its postcondition describes the actual returned
word and shared-state effects. It requires neither a `main` nor stream input/output.
`Ram.Source.FunctionExec` defines those observations through the function's real body and
return expression: the returned word must equal that expression's value after the body
executes. A mathematical specification is a property to prove about that execution,
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
the continuation receives the returned word, the proved postcondition and preserved caller locals.
The [local-binding sample](##Examples.Ram.LocalBindings) composes that rule twice
through `ram_total_apply`. Its direct proof uses the source declaration from
[getting started](##ComplexityDocs.GettingStarted) and the existing `square_contract`:

```lean
theorem squaredNorm_contract (heapLimit : Nat) (x y : Word w) :
    Source.FunctionContract functions.program heapLimit 1 functions.function.squaredNorm
      (fun args _ => args = functions.arguments.squaredNorm x y)
      (fun _ entry value finish => value = x * x + y * y ∧ finish = entry) := by
  ram_total_vc args entry rfl [functions.body_eq.squaredNorm, functions.result_eq.squaredNorm]
  ram_total_apply (square_contract heapLimit x) [functions.function_lookup.square]
  ram_total_apply (square_contract heapLimit y) [functions.function_lookup.square]
```

`ram_total_vc args entry pattern [facts]` starts the `FunctionContract` using
`Ram.Source.FunctionContract.of_wp`: declared arguments are bound, and the
postcondition observes the real return expression and shared state. The pattern
`rfl` here substitutes the specified argument list. Each `ram_total_apply` uses
the supplied function contract and lookup fact without unfolding `square`'s body.
Here simplification automatically substitutes the postcondition's equalities for
the returned value and final state into the continuation. No manual `rintro` or
final `rfl` is needed. Non-equational postconditions still leave ordinary continuation
goals. This proof needs no separate intermediate-state specification, register
arithmetic or stack layout.
Unresolved arity, frame and safety obligations remain explicit. `of_body` remains
useful when a body refinement or invariant is already available; the tactics do not
discover invariants or select reusable contracts automatically.
The sample's independent `squaredNorm_bodyTime` theorem identifies the same body's count
as 46. It includes both calls to `square`, not `squaredNorm`'s own final return expression
or its enclosing calling convention.

For a named declaration `p`, use `p.eval.f` for function-value equations and
`p.bodyTime.f` for separate body-count equations. These generated entry points take
the declared word or array parameters, then `heapLimit` and `entry`. They specialize
`Ram.Func.eval` and `Ram.Func.bodyTime`, observing the same actual invocation through
mathlib's `Part`. The value equation has the form
`p.eval.f ... heapLimit entry = Part.some (value, finish)` and includes termination;
the returned word and shared state are both retained. The
[factorial function-value sample](##Examples.Ram.FactorialFunction) hides its canonical
entry state once and proves agreement with every actual caller state. Subsequent
mathematical propositions mention only its argument and observed value.
This is a noncomputable proof view, not executable ordinary Lean function syntax.
General stateful functions still depend on shared entry state, and insufficient heap
capacity can make an observation undefined.

`Ram.Source.FunctionContract.eval_spec` transports any postcondition to that view;
the postcondition can be a mathematical relation, not necessarily a reference algorithm.
`Ram.Source.FunctionContract.eval_with_timeBound` adds a separate bound to the same
invocation's `Ram.Func.bodyTime`. Neither observation is defined using the proposed
result property or time bound. Body time excludes this function's own final return
expression and enclosing call overhead; it includes completed calls inside its body.

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

For a read-only scalar accumulation, [the shared fold](##Complexity.Computability.Ram.Array.Fold)
provides cursor progress, termination and framing. A client proves that its actual
source expression implements the mathematical fold step, that its reads are safe,
and that any extra read-only parameter remains unchanged. Sum and count both use
this rule. The separate measured rule derives iteration costs from the expression's
compiled instructions; a host-language callback is not accepted as a free operation.
The [count client](##Examples.Ram.ArrayCount) then derives permutation invariance
directly from `List.Perm.count_eq`. It uses the typed reference contract for
`count(xs : array, target)`, with independently represented arrays that may live in
different heaps. The theorem equates returned counts, not the states or the work needed
to construct those arrays. Mutating, short-circuiting and call-based folds still require
further interfaces.

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
`mvcgen` verifies the mathematical model: it does not compile arbitrary Lean code or discharge
the model-to-memory connection. Reuse an existing bridge where one is available.

## Automate the routine work

`ram_refine x s hs [facts]` starts a refinement proof;
`ram_total_vc s pattern [facts]` starts a state-based total-contract proof;
`ram_total_vc args entry pattern [facts]` starts a `FunctionContract` directly.
Precondition patterns include `rfl` and `⟨rfl, hbound⟩`. Closed frame bounds may
be discharged automatically; unresolved obligations remain ordinary Lean goals.
Use `ram_total_apply contract [facts]` to apply a supplied operation, function or
recursive specification while keeping its implementation opaque. The facts can
include generated lookup equations and known arity or local-frame facts.
`ram_model [facts]` simplifies observations, and `ram_word [facts]` normalizes word arithmetic
with the available range conditions. Remaining obligations are ordinary Lean goals.

Supply representation equations and mathematical facts through these tactic arguments or
Lean's usual `simp` mechanism. The tactics do not infer loop invariants, invent no-overflow
hypotheses or turn modular arithmetic into exact arithmetic. Their API is under
[total verification](##Complexity.Tactic.Ram.Total) and
[model simplification](##Complexity.Tactic.Ram.Model).

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
