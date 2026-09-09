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

## Independent source proofs

The new [typed core](##Complexity.Language.Basic) has its own
[finite execution semantics](##Complexity.Language.Semantics), independent of RAM.
`Complexity.Language.TotalWP` has separate normal-continuation and return
postconditions; faults cannot satisfy it. `FunctionTotal` requires an actual
returned value, with no proposed instruction bound. See the
[source verification rules](##Complexity.Language.Verification).

The [named frontend](##Complexity.Language.Syntax) accepts scalar programs such as:

```lean
source_program Bounded where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if next ≤ limit then
      result := next
    else
      result := limit
    return result
```

It generates typed source bodies, ordinary curried semantic functions and one-step
equations such as `Bounded.boundedIncrement_eq`. Each equation exposes that function's
body in native `ExceptT Fault (StateT Heap Part)` `do` notation, retaining named callee actions.
It is deliberately not a simp rule: unfold one body explicitly, then reuse a
callee's specification instead of recursively expanding its implementation.
A result statement can be written as
`Bounded.boundedIncrement n limit = pure (min (n + 1) limit)`.
This is the actual source program's result, not a separately implemented answer.
The action equation quantifies over every initial heap and preserves its value;
it does not select an empty heap or assert zero execution cost.
These `Part` functions are noncomputable mathematical observations, not host
executables for `#eval`; execution still uses the compiled RAM runner.

Mutable bindings use ordinary Lean `do` in the generated equation. `x := value`
updates an existing local, and `x ← action` rebinds it to the result of a real
source call, read or slice. Branch joins retain outer updates; leaving a scope
drops only its inner bindings. Ordinary `let` and parameters are immutable.
Changing a buffer handle does not copy its contents or alter the heap.

[Evaluation adequacy](##Complexity.Language.Eval.Basic) distinguishes finite
faults from absence of a finite result. The
[composition equations](##Complexity.Language.Eval.Composition) preserve lexical
scope, actual callee results and early returns. The
[continuation interface](##Complexity.Language.Eval.Continuation) derives ordinary
monadic composition from the same evaluation: `Stmt.evalWith` runs its continuation
only after a normal outcome. Return and fault bypass it; function fallthrough is
the defined `.missingReturn` error. These proved rules justify the generated
function equations, without a second interpreter or a user-supplied host algorithm.

For example, the helper proof begins directly at its generated equation:

```lean
theorem increment_eval (n : Nat) :
    Bounded.increment n = pure (n + 1) := by
  rw [Bounded.increment_eq]
```

For native `Std.Do` reasoning, `open scoped Part.TotalCorrectness` activates the
[strict partial-value WP adapter](##Complexity.Control.Part). It requires an actual
returned value: divergence cannot establish a postcondition vacuously. The
[verification bridge](##Complexity.Language.Eval.Verification) proves source
`FunctionTotal` equivalent to ordinary result equations and to native `ExceptT`
Hoare triples with false fault postconditions. It reuses the standard transformer
instances; it does not make `mvcgen` prove source termination automatically.
Function preconditions take the initial heap, and postconditions relate it to
the returned value and final heap. The native triple fixes the initial heap as
a ghost rather than identifying it with the post-state. Calls retain the
callee's actual heap even on failure. The
[heap foundation](##Complexity.Language.Heap) supplies `Buffer.Contents`, whose
mathematical view is a native array; reads and writes correspond to `getElem`
and `Array.set`, retaining aliases. The
[RAM representation](##Complexity.Computability.Ram.Compiler.Language.Heap)
relates complete shared objects and their views to actual memory, preserving
the relation through successful reads and writes. Its placement is proof data,
not a runtime object table. The
[operation bridge](##Complexity.Computability.Ram.Compiler.Language.HeapOperation)
executes real dynamic load/store expressions and retains their compiler-derived
counts, without claiming runtime fault checks. The source language now accepts
borrowed-buffer length, reads, writes and relative slices; calls and compiled
execution retain their actual final heap rather than restoring the initial one.

The [buffer example](##Examples.Language.Buffer) reads an element, calls a
branching helper, writes the result and returns a slice. Its ordinary native-array
specification describes the update with `Array.set`. After rewriting the generated
function equation, native `mvcgen` composes the public `readM_spec`, `writeM_spec`
and `sliceM_spec`; the author supplies contents and bounds, not monad implementation
equations. The write rule also retains its real write equation for alias/frame
reasoning. `FunctionTotal.triple_spec` turns a supplied source function contract
into a native continuation rule without unfolding the callee. This does not yet
automatically synthesize a whole function's frame contract or a loop invariant.

The typed core also has an effectful-guard `Stmt.while`. Its guard is an actual
Boolean-producing block: it runs in the current state on every iteration, and
even its false exit retains local and heap updates. A normally completing body
repeats the loop; a return exits the enclosing function. A guard that falls
through without returning a Boolean faults. `TotalWP.while_wellFounded` and
`while_variant` require mathematical descent only after a full normal cycle,
not on a false exit or early return. These are source rules, without a time budget.
The [native loop interface](##Complexity.Language.Eval.Loop) gives a one-step
equation for the same `Stmt.action` and `Stmt.while_spec` for strict `Std.Do`
reasoning. Its guard and body are actual source blocks, not a second host loop.
Named loop syntax and an invariant interface over ordinary named locals are
still unfinished; this core support is not yet the ordinary-loop author experience.

The [compiled buffer invocation](##Examples.Language.BufferCompiled) reuses this
source proof and derives the read cell's range from the input heap representation.
Its separate bound concerns the same read/helper/write/slice program and its
actual returned descriptor and updated heap. Borrowed aliases remain allowed;
the example does not establish a general mutable-loop proof interface.

The [scalar example](##Examples.Language.Scalar) calls a real increment helper,
assigns a local in the selected branch, then proves its returned value equals `min (n + 1) limit`
using ordinary Nat facts. Its primary `increment_eval` and `boundedIncrement_eval`
proofs rewrite the generated equations; the latter reuses the helper result and
splits the mathematical comparison. The generated `P.f_total_iff` accepts ordinary
curried preconditions and postconditions and derives the contract required by
compilation. It uses `FunctionTotal.iff_eval` and the generic environment rules
internally; the caller does not manually open `Env` or repeat the correctness
proof. Direct source-WP rules remain available when a
compositional contract is the preferred starting point. The
[compiled invocation](##Examples.Language.ScalarCompiled) supplies only source-level
range and call-nesting facts, then reuses that mathematical proof. In particular,
`n + 1` must fit even when the final minimum is small. These conditions do not
include a proposed instruction budget. The
[structural tactics](##Complexity.Computability.Ram.Compiler.Language.Tactic)
now open ordinary parameters and compose the scalar realization rules:

```lean
ram_source_realize (n limit) using increment_realizable, increment_total
all_goals omega
```

The supplied callee facts remain opaque. Environment projections and argument
packing are simplified internally; genuine scalar ranges, callee preconditions
and sufficient call nesting remain mathematical goals. This is a scalar proof
pass, not automatic discovery of invariants or general recursive contracts.

[Generic simulation](##Complexity.Computability.Ram.Compiler.Language.Simulation)
handles lexical layouts, real callees and returned fields.
[Static validity](##Complexity.Computability.Ram.Compiler.Language.Validity)
chooses the register boundary and discharges checked-compilation conditions;
[execution transfer](##Complexity.Computability.Ram.Compiler.Language.Execution)
then gives the existing halted runner, actual result and same-execution count.
Code and stack capacity remain explicit. Shared-state preservation is derived
from the actual lowered program, not assumed from restored caller registers.

The compiler lowers each statement child once and uses a private return flag to
skip tails after a return; calls restore the caller's flag.
[Exact code-size formulas](##Complexity.Computability.Ram.Compiler.Language.CodeSize)
include each branch once, plus actual argument and callee-frame expansion.
Static code length is not elapsed time: the running program selects one branch,
and even a returned path pays the flag checks in enclosing sequences.

[Source cost rules](##Complexity.Computability.Ram.Compiler.Language.ExecutionCost)
now observe the same realized source execution. `ExecutionCost` counts its
lowered core; a complete function adds two transitions for flag initialization.
Its empty final dispatch has been removed, with a proved saving of three static
instructions and an unchanged register bound. The generic statement wrapper
with an external continuation still uses five additional transitions on return.
`callCost` derives internal-call overhead from the actual compiler, including
the callee body and frame, without a user-supplied ABI price.
The [measured simulation](##Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation)
proves these are real machine counts. Budget-free behavior simulation erases
this same proof instead of maintaining a second structural induction.

`FunctionCostBound` is a separate conditional bound: it does not establish
termination or repeat the mathematical postcondition. Its counts are
[independent of word width, call capacity and realization proofs](##Complexity.Computability.Ram.Compiler.Language.CostDeterministic).
[Cost transfer](##Complexity.Computability.Ram.Compiler.Language.CostExecution)
identifies the existing `bodyTime`; `FunctionRealizable.runUntil_le` combines
the source bound with the original correctness and realization contracts.
The complete invocation bound adds the outer calling convention and final halt
exactly once.

Use the [structural bound rules](##Complexity.Computability.Ram.Compiler.Language.CostBound)
to compose source costs. `StmtCostBound` bounds the existing execution observation;
its primitive, sequence, branch, return and call rules hide case analysis on
`ExecutionCost`. `FunctionCostBound.of_stmt` adds the returning-body wrapper once.
`ram_source_cost (n limit) using increment_costBound` applies these rules to the
scalar consumer and compares the inferred bound with its requested bound.
Its uniform bound needs no proof of the minimum;
result-dependent bounds can reuse an existing source contract through the call
rule. The tactic currently uses uniform bounds at branches and call
continuations; result-dependent bounds retain the explicit rule interface.
Neither instruction prices nor mathematical correctness proofs are duplicated.

For typed loops, `StmtCostBound.while` uses a state-dependent potential. The
guard and body bounds follow the actual state; normal iterations account for
the remaining potential, while false exits and early returns discharge their
own remaining work. The final false guard is counted. This is a conditional
cost rule for the same execution, separate from the well-founded termination
rule; the structural tactic does not yet choose or apply loop invariants.

The frontend currently supports `Nat`, `Bool`, `Unit`, borrowed buffers, lexical bindings, actual
named calls, branches and returns. Nested addition, multiplication, saturating
subtraction, division, remainder and comparisons are normalized left to right
into actual primitive bindings. This also applies to guards and call arguments.
The [remainder example](##Examples.Language.Remainder) implements
`n - (n / d) * d`, reuses the ordinary Nat identity, and derives the actual
compiled result with a separate instruction bound. Divisor zero is included;
no artificial subtraction-order condition is required.
Loop syntax, products and allocation remain future work. Local assignment is
covered by the same structural realization and cost tactics. Richer
callee selection, recursive proofs and data-dependent bound automation remain
unfinished. Costs are currently derived
for successfully realized executions, not an instrumentation theorem for
every unrestricted source execution.
M1 remains open: the scalar pass is useful but does not establish the complete
source proof and specification interface needed by mutable data and recursion.
Optimizing code size does not imply every execution is faster.
The executable word-RAM workflow and maintainer interfaces below remain available.

Compiler maintenance is a separate, active proof workflow. The
[layout rules](##Complexity.Computability.Ram.Compiler.Language.Layout),
[return-flag preservation](##Complexity.Computability.Ram.Compiler.Language.Control)
and measured simulation compose actual register updates and calling conventions.
The same layout indexes every actual value field. Parameter packing and fresh
receivers use those indices and the existing register-update rules; Unit has no
dummy field. Buffers have two fields, their actual base address and length;
arbitrary products are not enabled yet. Sequential multi-field copies preserve
their operands through proved destination separation or actual self-copy
identities, not an assumed snapshot. `RegisterMap.Regular` proves the field
layout needed to update an existing variable without changing another live
variable; parameter layouts and fresh bindings supply it automatically.
Maintainers may use these lemmas directly, without frontend metadata. Preserving
caller registers does not imply that a callee leaves memory or I/O unchanged.
The [frame-effect rules](##Complexity.Computability.Ram.Compiler.Effects) include
`FramePreserved.frameSaved`: a saved caller frame within the protected stack
interval remains valid after the callee. Ordinary and local call proofs reuse
this rule, while retaining genuine heap effects and address bounds.

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

The same `ram_total_vc` supports `TypedFunctionContract` through its `of_wp` rule.
The [three-array merge](##Complexity.Computability.Ram.Array.Merge.Function) uses
`ram_total_vc` and `ram_total_apply` to call the already verified core: the remaining
goals are its three represented arrays and the post-call list representations.
It does not need another typed tactic or a second proof of the merge loop.

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
these two conveniences remain specialized scalar folds. General bodies use the
invariant rule below; short-circuiting still needs a separate language interface.

These rules operate on fixed source statements. They do not turn an arbitrary mathematical
function into executable code. See [data models](##ComplexityDocs.Models) for array, matrix,
partial-map and framing interfaces.

## Loops and recursive calls

For a loop, choose a mathematical invariant and a well-founded progress argument.
`Ram.Source.Refines.while_wellFounded` relates the real guard and body to an abstract step
and eventual result. If a decreasing natural number is enough,
`Ram.Source.Verification.TotalWP.while_variant` provides a direct total-correctness rule.
The guard, representation and safety obligations remain at the implementation boundary.

For an arbitrary body of `Stmt.forIn`,
`Ram.Source.Verification.TotalWP.forIn` handles setup, each actual element load
and the two cursor updates. Supply an invariant at the loop head and prove the
body from `ForIn.loadedState` into an invariant after `ForIn.advanceState`.
The body must preserve the remaining count of its loaded entry state. The rule
uses ordinary natural descent, not a proposed time budget. The invariant need
not describe a single accumulator or unchanged heap: it can relate several
locals and mutable data to ordinary mathematical values.

This is an implementation-side combinator, not automatic invariant inference.
The loop-head invariant is not assumed to survive the element assignment.
Each load reads the current heap; body effects reach the next iteration.
Initialization evaluates length after assigning the pointer, and address safety
is required only when the guard is nonzero. The rule does not assert that an
arbitrary body preserves the original array contents or pointer trajectory.
See [general foreach correctness](##Complexity.Computability.Ram.Verification.ForIn).

For a forward traversal that preserves its private cursor locals, prefer
`Ram.Source.Verification.TotalWP.forIn_indexed`. Supply a payload
`invariant : Nat → State w → Prop` for the mathematical iteration number.
The rule owns the pointer/count relation, count subtraction, termination and
exit-index argument. The body proof receives `i < n` and the payload at the
pre-load state, starts at the actual current-heap element load, and establishes
the next payload after `ForIn.advanceState`. It does not assume the payload
survives loading its element local. Cursor preservation is an endpoint premise,
so writing and restoring a cursor is allowed; static destination exclusion is
one way to prove it. Memory and I/O may change. The setup equations still use
sequential expression evaluation, and only executed addresses need be safe.

If the payload is insensitive to the two private cursor locals, use
`Ram.Source.Verification.TotalWP.forIn_indexed_of_frame`. Prove once that
`State.LocalFrame {pointer, remaining}` preserves it. Then initialization starts
from the original state and the body only proves `invariant (i + 1)` at its own
endpoint; the shared rule transports this through cursor setup and advance.
Only those generated assignments use the unchanged-shared-state frame, not the
arbitrary body. Map uses this interface without unfolding `advanceState`.

The independent `Ram.Source.TimeBound.forIn` accepts a uniform conditional body
bound `B` and preservation of the remaining count on completed body executions.
It adds the actual setup expression lengths, `(B + 14) * count` and the remaining
four setup/final-guard instructions. No body totality or heap-purity premise is
needed for this conditional result. The existing helper-call traversal reuses
this rule; its separate prefix-dependent bounds remain available.
See [general foreach costs](##Complexity.Computability.Ram.Verification.Time.ForIn).

The [in-place map operation](##Complexity.Computability.Ram.Array.Map.Function)
is a mutable consumer of these rules. Its typed contract takes a borrowed array,
returns `Unit`, and produces a representation of `xs.map transform` together
with the outside-array frame and preserved I/O. The helper is a statically linked
source function, proved to implement `transform` on the original list elements.
The mathematical function is only its specification, not a runtime callback.

The [map client](##Examples.Ram.ArrayMap) uses the existing DSL:

```text
fn mapSquares(xs : array) : Unit {
  for i, x in xs {
    let y ← call Scalar.square(x);
    xs[i] := y;
  }
  return;
}
```

Its correctness proof reuses the imported square contract and the common map
theorem. Index initialization and increment are real generated assignments;
both loop bindings stay within the body. The operation proof uses the indexed
rule to maintain the ordinary
updated-prefix/unread-suffix list without its own private cursor/count invariant.
The body directly composes a function-call WP, `Ram.Source.Array.store_contract`
with its count forgotten, and an assignment WP. The continuation receives the
updated `List.set` representation and frame instead of rebuilding an execution
endpoint. It reads each original element before replacing it.
Empty arrays are admitted; an unused final pointer may wrap
at the address-space endpoint. The actual descriptor length remains word-sized.

The independent map bound is `(C + 23) * length + 8`, where `C` is the helper's
proved body bound plus its actual compiled calling overhead. It requires a
uniform conditional helper bound on one-word inputs, not helper totality.
For this imported square, the full compiled invocation has bound
`46 * xs.length + 71`; `applyState_contents` observes `List.map` from the same run.
The map changes memory, so a returned `Unit` alone is not its mathematical output.
No host list loading or allocation is included.

This is a reusable operation, not a general named-invariant elaborator or runtime
higher-order function. Arbitrary mutable bodies still use the explicit invariant
rule; input-dependent helper costs need a corresponding ordered cost proof.

For local binding adapters, `Ram.Source.State.LocalFrame writes before after`
packages unchanged memory and I/O with mathlib's
`Set.EqOn after.regs before.regs writesᶜ`. Its assignment and composition rules
let a proof carry all unaffected parameters together instead of rebuilding a
chain of individual register updates. This is an endpoint relation, not an
execution or a description of every write event. An expression still needs its
read-safety and evaluation proof, and every actual assignment keeps its cost.

Function entry initializes the entire local frame. To reason that new locals
preserve parameters, compare subsequent states with `entry.enter args`, not
with the original caller's register bank. `State.restore_eq_of_shared` uses
proved memory/input/output equalities to restore the original caller without
requiring preservation of discarded callee locals. See the
[local-frame rules](##Complexity.Computability.Ram.Source.State.Frame).

For effectful bodies, `SafeExec.regs_eq_of_not_mem_writtenRegs` instead preserves
each local outside `Stmt.writtenRegs`, without requiring an unchanged heap.
The [static local-frame rules](##Complexity.Computability.Ram.Source.Frame) use
ordinary sets and include only result destinations for calls. Map and helper-call
traversal discharge their count-preservation condition by simplifying this set,
not inspecting callee executions. Static exclusion is sufficient, not necessary;
the original semantic rule still admits writing and restoring a local.

The [named search](##Complexity.Computability.Ram.Array.Search.Function) directly
opens its generated body, proves initialization, and reuses the shared loop
contract. Its time proof follows the same source decomposition. The actual
remaining `while` determines the private local slots before their separation
is checked; no extra function-body recognizer or exported loop-scoped midpoint
is needed. The shared mathematical invariant and its initialization proof remain
explicit, so this is not general automatic invariant discovery.

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

For a named function whose initialization needs mathematical reasoning, use
`ram_total_start args entry pattern` to apply the existing function rule without
advancing the body. Then

```lean
ram_total_init functions.function.lowerBound at initial with bindings
```

follows the actual leading assignment statements, stopping before calls or
control flow. `initial` names the current source state. The visible locals
become ordinary Lean values such as `initial.xs : ArrayRef w` and
`initial.lo : Word w`; `bindings.xs.base`, `bindings.xs.length` and `bindings.lo`
relate these values to their actual source bindings. Nested locals such as the
search midpoint are not visible before entering their scope. An array local is
exposed only after its two field assignments have both executed.

The [named search proof](##Complexity.Computability.Ram.Array.Search.Function)
uses these facts with `Search.Pre.invariant`, then applies its existing loop
contract. It does not write a separate `State.enter`/`setReg` initializer.
The independent time proof uses `ram_time_start` and `ram_time_init` with the
same syntax, but applies the existing conditional time rules and charges the
actual assignments. Both initialization forms accept optional `[facts]`;
unsolved safety or affordability goals remain explicit. Neither form invents a
loop invariant or advances through a call.

To enter the next source conditional, select its branch explicitly:

```text
ram_total_branch f then at current with bindings [facts]
ram_total_branch f else at current with bindings [facts]
ram_time_branch f then at current with bindings [facts]
ram_time_branch f else at current with bindings [facts]
```

`then` requires the actual guard to be nonzero; `else` requires it to be zero.
Selecting a branch does not assume that condition: unresolved guard, read-safety
or time-affordability obligations remain ordinary goals. The step enters that
branch's lexical scope and advances its leading initializers, stopping before
another conditional, call, loop or other effect. Statements following the
conditional are retained; an omitted `else` executes the actual empty branch.

The [recursive sort implementation](##Complexity.Computability.Ram.Array.MergeSort.Function)
starts its large-input case with `ram_total_start`, followed by
`ram_total_branch sortFunctions.function.sort then at initial with bindings`.
Supplied range facts prove the guard. The actual source declarations then produce
`initial.middle : Word w` and `initial.left`, `initial.right : ArrayRef w`.
Both descriptor assignments complete before an array local becomes visible.
These values are passed to the existing recursive and merge contracts; no raw
slots or separately reconstructed initializer state are needed. Halving,
slice containment, disjointness and changed-heap reassembly are still proved
with the existing mathematical lemmas.

The [separate time proof](##Complexity.Computability.Ram.Array.MergeSort.FunctionTime)
uses `ram_time_start` and the corresponding `ram_time_branch`. Its rules retain
the actual guard evaluation, branch jumps and field-assignment costs; they bound
completed executions without using the initialization's total-correctness proof.
The proof starts from the original whole-body bound, with no hand-selected
intermediate branch reserve. The recurrence and proof that the complete work
fits that bound remain explicit, while remaining allowances follow from the
actual operations.

Without a cursor, these entry points require the named function's whole body.
An initialization or branch step records its exact lexical block and next child
only on the remaining code goal, so another such step can continue there.
The actual code is rechecked at that fixed position: no search for an equal AST
or re-elaboration of embedded source terms is used. This does not locate an
arbitrary prefix after unrelated proof tactics have advanced it.

The generated Lean lets are snapshots at the named state, not live readers of
later registers or heap contents. They remain usable in ordinary call proofs;
sort's `Unit` calls restore the caller locals containing its descriptors.
Representations of changed arrays still require the actual callee postcondition.
Ordinary call tactics do not advance the source cursor or automatically bind a
new source-local result name. Entering loaded loop-body scopes and elaborating
source-level invariants remain unfinished. See
[source-directed initialization and branches](##Complexity.Tactic.Ram.Source).

For a typed function call, `ram_total_apply contract on input [facts]` selects
the actual mathematical input and passes the returned value and shared effects
to a continuation with caller locals restored. It only attempts to close the
lookup, result-count, argument-read and argument-value obligations completely,
using declaration equations and locally generated source-binding facts.
The functional precondition, call-depth condition and continuation retain their
original form. In particular, supplying a slice definition to match runtime
arguments does not also expand every represented slice in the continuation.
Merge sort uses this form for both recursive calls, merge and copy-back.

Use `ram_total_store represented at index := value [facts]` to write one element
of a represented array. It applies the existing array-store contract to the
actual `TotalWP` store, opening one leading sequence when needed. No address
expression, value expression or destination register needs to be repeated.
The continuation retains the real updated state, a representation of
`contents.set index value`, and the outside-array frame. The
[map implementation](##Complexity.Computability.Ram.Array.Map.Correctness) uses:

```lean
ram_total_store h.array at i := (transform xs[i])
  [indexFits, h.base_eq, h.index, arrayAddr]
```

Only completely solved side conditions are discharged. Index bounds, current
representation, read safety and address/value equations otherwise remain visible;
the continuation is not simplified. A representation survives local-register
changes by its definition, but cannot be reused across a genuinely changed heap
without a proof. The tactic neither advances the next statement nor supplies
the next invariant. See [array automation](##Complexity.Tactic.Ram.Array).

Use `ram_total_bind mid hmid [definitions, facts]` on a `TotalWP` assignment
or a sequence beginning with one to name that assignment's actual word value.
The continuation receives `mid` and `hmid : mid = entry.eval expression` without
expanding the value or advancing later statements. The optional list unfolds
only the supplied definitions before applying the rule. Read safety is closed
only when `ram_simp` proves it; otherwise it remains a separate goal.
The [search body proof](##Complexity.Computability.Ram.Array.Search.Total) uses
this to reason about one named midpoint in both branches. The name is local to
the proof continuation, not an exported loop variable; array-result binding,
layout inference and invariant inference are not supplied by this tactic.

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

The public `Ram.Source.Array.copy_function_typed_contract_of_ref` accepts a proof-level
pair of array references, encoding the same source pointer, destination pointer
and source length. Its destination length follows from represented input and
the equal-length premise, not a fourth runtime argument. The result is `Unit`. The sample
relocates this contract and applies its `wp_call_restored` rule with
`ram_total_apply`; declaration-generated bindings supply the lookup facts.
Copy's postcondition supplies both complete `ArrayRef.Rep` assertions, including the one needed by sum,
whose contract is reused through `functions.embeds.Sum`. The standalone
`call Copy.copy(...);` has an empty result list and no dummy destination.
Its postcondition and shared-memory effects still reach the continuation through
the same call rule. This differs from discarding a word or array result, whose
fields are still evaluated and received into private destinations.
Relocation does not discharge representation, equal-length or
disjointness premises. The proof composes the existing contracts without expanding
either callee loop; the generated `applyState` result belongs to one compiled run,
unlike the host-level sequencing in `ArrayCopyFunction`.
Merge sort's final copy uses this same reference contract. The raw and word-triple
typed contracts remain available; neither source signature nor execution cost changes.

The same sample's `imported_sumPair_eval` transports the existing two-array execution
through `functions.embeds.Sum` to `functions.eval.Sum.sumPair`. This also exercises
relocation of the imported function's own two calls to sum, without reopening them
or their loops. Imported aliases export lookup, argument and all six observation/run
interfaces; body equations and local-register names remain with the original declaration.
Generated `params_eq` and `locals_eq` equations are also available under imported
aliases. They expose calling-convention sizes without unfolding the callee body.
The separate time proof reuses the same functional postcondition: `ram_time_apply`
with `on input` passes copy's destination representation through restored caller
bindings and derives the remaining sum-call reserve from the overall body bound.
The proof still establishes that the complete copy call fits; neither a register
equality nor a hand-selected intermediate reserve is needed. The bound belongs
only to the time proof, not the correctness contract or executable call.
See [proving complexity](##ComplexityDocs.Complexity).

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

If a continuation has a uniform bound at every intermediate state,
`Ram.Source.TimeBound.seq_const` adds its bound to the first command's bound
without requesting a functional contract. Map uses this for its actual
store/assignment tail. State-dependent continuation bounds still need the
relevant intermediate facts; the uniform rule does not establish them.

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
