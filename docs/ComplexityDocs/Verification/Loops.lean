/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.Factorial
import Examples.Language.FactorialCompiled
import Examples.Language.LinkedList
import Examples.Language.LinkedListCompiled
import Examples.Language.ScalarCompiled
import Examples.Language.Traversal
import Examples.Language.TraversalCompiled

/-!
# Source loops and recursion

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## While contracts and termination

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
The [ordinary-local view](##Complexity.Language.Eval.Locals) represents the complete
lexical environment by ordinary values, retaining the final locals on every
exit. Its [loop rules](##Complexity.Language.Eval.Locals.Verification) take an
invariant and well-founded relation, or a natural-valued variant, on those values
and the current heap. The [continuation bridge](##Complexity.Language.Eval.Locals.Continuation)
runs the remaining function only on normal completion. These are proved changes
of view of the same source execution, not another implementation.
Named `while` and bounded `for` generate actual guard/body/loop observations,
one-step equations and mathematical block contracts. A `guard_contract` describes
the Boolean decision and actual state after testing; a separate `body_contract`
describes normal completion or early return. Their predicates take ordinary
mutable arguments and initial/final heaps. They are native strict triples,
packaged by [BlockSpec](##Complexity.Language.Eval.Locals.Specification), not a
second operational semantics.

Use `variant_contract` to compose these facts with a natural-valued measure,
or `wellFounded_contract` with an ordinary Lean well-founded relation. The body
starts at the actual post-guard state; a normal iteration must decrease relative
to the state before the guard. False exits and early returns need no descent.
Generated `guard_spec`, `body_spec` and `spec` apply a chosen contract to a native
continuation. Immutable captures are restored internally from proved execution
frames; preserving a buffer descriptor does not preserve its contents.
The older `variant_spec` and `wellFounded_spec` rules remain available for direct
native round proofs. None of these
source rules asks for fuel or an instruction budget.

For a traversal with a natural count increasing by one, `count_frame_contract`
composes the existing guard/body contracts with a transitive heap relation.
Supply the count, its fixed upper bound, the invariant, the per-step frame and
the exit consequence. The shared rule proves descent by the remaining count
and accumulates the frame from the supplied initial heap, which need not be the
current loop-entry heap. The guard contract must preserve the count and heap
and establish the invariant at its actual output; other mutable locals may
change. The body contract must exclude early returns. The
[borrowed traversal](##Examples.Language.Traversal) and
[buffer copy](##Complexity.Language.Buffer.Copy) use this entry without manual
guard/body consequence rules. Array updates, bounds and disjointness remain
their mathematical obligations; no effects or cost bounds are inferred.

### Mathematical locals for represented rounds

When a normal loop round has checked mathematical operation contracts, the
frontend also generates `Model`, `modelGuard`, `modelStep`, `model_contract`
and `model_spec` under the same named source loop. `mkModel` accepts source-variable
parameter names; `model_<name>` reads a mathematical local. The representation
of that local at the actual heap is available through `<name>_representation`
and `model_rel_<name>`. Complete source coordinates remain in the connection
proof, not in the author's invariant.

The [array-record loop](##Examples.Language.LinkedList) uses, for example,

```lean
let invariant : Model → Prop := fun model =>
  (model_state model).copies + model_remaining model = initialValue.copies + count
```

The author proves preservation under `modelStep`, descent when `modelGuard` is
true, and the desired result when it is false. `model_spec` then supplies the
actual loop contract to `mvcgen`. The generated round proofs compose existing
operation correspondence and preservation contracts at the actual intermediate
heaps; no `Part.bind` or raw environment transport is supplied by this consumer.

This pure-round interface requires justified preservation of captured array
observations. It needs no pure model of the complete loop, adds no source helper
calls and does not infer a RAM bound.

For local-return rounds, the same source-field representations generate `Model`,
`mkModel` and field observations without requiring a pure round trace.
`guard_model_contract` and `body_model_contract` lift supplied source contracts
to mathematical locals at the actual heaps. An author chooses a mathematical
index and `encode : Index → Model`; captures can remain ordinary parameters.
`model_completion_contract` then combines the guard/body contracts, a
heap-dependent invariant, a mathematical progress relation and its well-founded
decrease, and the normal/completed result predicates.

The [scoped worker loop](##Examples.Language.Scope) uses its remaining count as
the index and `mkModel`'s source-variable names to select its state. Its proof
reuses the worker's real contents contract and ordinary invariant lemmas,
without tuple, `Part` or hidden-entry transport. A completed body needs no next
invariant or decrease. The rule requires the supplied guard contract to preserve
the mathematical index and actual heap; it may use the current invariant to
justify its accesses. No heap-preservation restriction is imposed on the body.
For a guard that changes locals or the heap, use `model_completion_effects_contract`.
Its supplied `prepared before initial tested after` relates the round's input to
the guard's actual output. The body contract starts at `tested, after`; only a
continuing body must reestablish the invariant and decrease relative to `before`.
A false guard supplies the exit condition at its own final heap. The simpler
`model_completion_contract` is a specialization of this rule. This composition
does not infer the guard's effects or a frame for aliased observations. A raw
`Buffer` field observes its handle, not unchanged contents, and this interface
does not turn aliased mutation into an assumed pure transition. The completed
result remains the actual source return value; its contents are proved by the
result predicate, not automatically converted into a mathematical Array or List.

For complete identity-represented locals, `guard_model_contract_iff` and
`body_model_contract_iff` turn these contracts into native triples over `Model`.
Use the corresponding actual guard/body equation and `mvcgen` with the real
operation contracts. The generated `modelEquiv` only rearranges source fields;
`guard_model_action` and `body_model_action` map the result of the existing
action, preserving its control and heap. They are proof observations, not
additional source programs. The scoped loop proves its guard/body facts this
way and reuses them for both loop correctness and resource composition; its
older visible-local theorems are short compatibility consequences.
This direct triple entry currently requires a complete identity representation.
General Array/List observations retain their heap-indexed relational contracts.

## Finite ranges and resource rules

Represented finite ranges with normally continuing, fully modeled bodies have
an ordinary `List.foldl` view, including allocating List iterations inside a
typed local `do` value block. The generated proof retains the real loop's
pending-controlled guard and increment and proves the result slot stays empty;
authors do not expose that slot in their mathematical proof. The existing
[List range](##Examples.Language.LinkedList) keeps its replicate equation in
this form.

Fully modeled `if`/`Option` rounds that may return from the local value block,
including nested mixed return/continue branches, use a control-sensitive
`Option payload × state` summary and Lean `forIn` instead of a fold. Its
heap-indexed correspondence observes the same actual body result and final locals:
the active pending slot may change, while ancestor
slots and fixed captures remain preserved. The payload type is the local block's
result type, independent of the enclosing function's return type. Continuing
rounds advance the cursor; completed rounds exit through the real masked guard
without running another body or inventing a decrease. The remaining statements
inside the local block run only when no result was saved. This adds no second
source loop or allocation for proof-side state; actual body allocations and control instructions remain
part of the compiled program. Branch summaries carry only mutable lexical slots,
including shadowed bindings; immutable observations use proved heap preservation.
The shared proof boundary for supported typed `do`, `if` and Option/List `match`
value bindings lets finite-range/Option models carry updated outer mutable bindings
alongside the terminal payload. The code after the binding consumes both through
their actual heap-indexed relation, retaining the original raw return markers and
joins; this is not an unchanged-heap exact equation or a general `while` model.

The prepared completion-range mathematical `forIn` carries
`Option Result × Mutable`: the iteration index remains a callback argument, but
the cursor is erased from the accumulator and immutable captures are closed over.
`Stmt.forIn_range_step_completion_eq` reuses `forIn_range_hom` twice to connect
this view to the full state, requiring fixed-field preservation on both continuing
and completing rounds. Its step still projects the full mathematical body result.
For functions whose trace contains a completion range, `Family.f_model_eq` exposes
a locally reduced body of `Family.f_model`, or `Family.f` in `(native)` mode.
Use the equation explicitly; it is not registered as a global simp rule.
It moves `Prod.map` through `Option.elim`/`if` using `Option.elim_comp` and
`apply_ite`, and reduces `Id` pure/bind and concrete tuples. This removes the
per-field callback connection proof in the checked List consumer while retaining
its mathematical induction; nested branches are also checked. It does not
promise a simplest normal form for arbitrary callbacks. The same source loop,
actual heap and body trace remain the basis of correspondence and resource proofs.

The default represented frontend also gives fully modeled finite-range bodies
with mixed `if`/`Option` branches a mathematical model and checked correspondence
for direct function returns. This uses the actual `Control.returned`/`whileReturn`
path, not an added local value block or pending-result slot. A returned (`some`)
round keeps the real payload and endpoint heap without advancing the cursor or
running an extra false guard. Raw lowering is unchanged; the mathematical model
does not select another returned value or executable loop.

Automatic action correspondence and refinement are also checked for a two-level
finite-range nest with an inner function return, retaining actual payloads,
locals and heaps. A completed `forIn` result may be shared in the proof when
composing the continuation; this adds no executable binding or changed cost.
Normal and function-returning finite ranges also compose enclosing self-calls with
descent from fixed captures or the actual range bound. Correspondence uses actual
fixed slots and representation functionality at the current heap to recover those
captures; arrays still need contents frames.
Broader nested-loop combinations, mixed local/function completion and full models
of arbitrary heap mutation remain open.
None of these mathematical range views infers a RAM bound for its body or control.

For pure finite Nat ranges, the shared
[`while_range_encoded_invariant`](##Ram.LanguageCompiler.RealizationWP.while_range_encoded_invariant)
rule reuses generated native correspondence and retains the supplied mathematical
invariant at normal exit. It supplies range termination, leaving the actual
guard/body word conditions and invariant preservation to the client. The
[structured accumulator](##Examples.Language.ScalarCompiled) uses it to connect
ordinary fold/sum correctness and its independent full invocation bound to the
same halted RAM result. In addition to launch capacity, its range conditions
include the final sum, computed stride and last actual cursor, which may exceed
the stopping endpoint. Its connection proof still selects generated local views;
that remaining transport is not a new mathematical proof of the algorithm.

The [loop-coordinate tactic](##Complexity.Computability.Ram.Compiler.Language.LocalsTactic)
normalizes generated local views without repeating their projection lemmas:

```lean
ram_source_locals StructuredRange.sum_loop1
ram_source_locals Implementation.boundedMap_loop1 at bound
```

The loop namespace selects its registered coordinate, native-encoding and frozen
range-endpoint equations. Standard locations also support `at h ⊢` and `at *`;
without a location only the target is rewritten. The tactic does not unfold
program bodies, callees, invariants, value-range predicates or costs, and does
not search for arithmetic proofs. Both the structured accumulator and mutable
traversal use this pass. Selecting the loop contracts and supplying their
mathematical obligations remain separate from coordinate normalization.

For a statement goal retaining its generated loop `Code`, the
[named-loop resource tactics](##Complexity.Computability.Ram.Compiler.Language.LoopTactic)
also select the capture view and its checked guard/body preservation proofs:

```lean
ram_source_loop_cost (remaining := fun locals _ => contents.size - locals.1)
  using (guard_contract xs limit contents), (body_contract xs limit contents)
  costs guard_costBound, body_costBound

ram_source_loop_realize
  using (guard_contract xs limit contents), (body_contract xs limit contents)
  total loop_contract xs limit contents heap
```

The supplied block contracts determine the invariant and actual guard/body
relations. The cost form applies uniform guard/body certificates; the author
still proves entry into the body, invariant preservation, decrease, positivity
and the initial invariant. The realization form converts the source loop
contract to totality, keeping its precondition separate from the resource
invariant. For example, the traversal's source precondition additionally carries
its outside-buffer frame. Routine true/false postcondition consequences are
discharged; other consequences, actual word/nesting proofs and invariant
preservation remain goals. The `enterBody` case names the true-guard implication.
The compiled traversal uses both entries without writing capture views, frame
theorem names, environment repacking or its own `BlockSpec → TotalWP` conversion.
Mathematical mutable-coordinate patterns remain in its proof leaves.

Apply these tactics before unfolding the named `Code`. Already expanded loops
and arbitrary potential functions can still use the public loop theorems below;
the cost tactic is the uniform-cost, linear-iteration specialization, not a
replacement for those general interfaces or automatic invariant discovery.

For a named local-return loop with mathematical guard/body contracts and an
existing finite execution, use

```lean
ram_source_loop_arena_model (encode := loopModel out count n value)
  using (fun left heap _ =>
    guard_model_spec out count n value left (fun current => current = heap)),
    (fun left heap current active => body_model_spec out count n value
      (remaining := left) (heap := heap) current (of_decide_eq_true active))
```

This entry selects the actual named loop and reuses its source contracts through
`ArenaReady.while_completion_model_of_exec`. The supplied contracts determine
the invariant, test, transition and completed result relation. There is no
second invariant-preservation or termination proof. The remaining leaves are
the real guard/body readiness, saved-result readiness, entry invariant and
successful-control condition. For a complete identity representation, a proved
correspondence removes raw entry coordinates from guard/body leaves. A general
heap-indexed representation remains a relation; there is no inferred inverse
from mathematical array contents to a unique handle.

The general
[`ArenaReady.while_completion_model_effects_of_exec`](##Ram.LanguageCompiler.ArenaReady.while_completion_model_effects_of_exec)
accepts the same effectful guard/body contracts and adds readiness at the actual
post-guard model and heap. It reuses the given finite execution without requiring
descent again. The preserving-guard rule above is a specialization. This is still
a fixed-cursor rule: heap mutation and reclaimed scratch are allowed, but retained
allocation cannot silently reset the cursor. The named tactic above selects the
preserving specialization; the general rule is currently used directly.

The lower-level visible-local entry remains available:

```lean
ram_source_loop_arena (stateRel := invariantRelation)
  (prepared := bodyPrecondition) (completed := resultPostcondition)
```

The three relations concern visible source locals and actual heaps. This entry
selects the registered completion coordinates and execution frames, then applies
`ArenaReady.while_completion_of_exec`. Guard/body source contracts, their real
resource readiness, readiness of the final stopped guard, and the initial facts
remain obligations. Neither entry reconstructs private completion slots in the
author's proof or asks for loop termination again. Both preserve the same arena boundary between rounds,
not arbitrary growing allocation, and does not infer a time budget.
For the final stopped guard, `RealizationWP.localReturn_guard_some` uses the
saved result's actual word-range proof. It follows the option match and false
return without evaluating the original test; `.arenaReady` then applies this
fact to the same finite execution. The scoped consumer needs no private proof
about the compiler's payload slot for this branch.

For the actual named `Guard` or `Body`, `ram_source_fragment_realize` normalizes
registered source coordinates and runs the existing structural realization pass.
For a standalone call followed by a fixed-placement continuation, use:

```lean
ram_source_fragment_arena_call using (by
  intro finish returned called
  cases returned
  exact work_ready out n value heap hw outRooted outFits nFits valueFits capacity called)
all_goals omega
```

This is the scoped consumer's actual worker certificate; the `cases` only
eliminates its `Unit` result, not an execution tree. The shared
[`ArenaReady.call_seq_of_exec`](##Ram.LanguageCompiler.ArenaReady.call_seq_of_exec)
handles the call and sequence, keeping the callee's real final heap and restoring
caller locals. Argument ranges are normalized into ordinary goals. The tactic
retains the callee's arena cursor through the continuation; allocating
continuations use the general rule directly. It does not infer callee contracts,
capacity, loop invariants or time bounds.

## Reuse a traversal invariant

The [read/helper/branch/write traversal](##Examples.Language.Traversal) writes
`for i in [:xs.length]`. Its invariant describes the processed prefix and unread
suffix of an ordinary array. Independent guard/body contracts feed the loop
contract; the author proves array identities, actual frames and descent rather
than constructing a nested triple for a whole iteration. The generated `spec`
then composes that contract with the function's continuation. Selecting these
contracts and mathematical contents remains explicit. The
[compiled traversal](##Examples.Language.TraversalCompiled) reuses this source
proof to establish the same array result and an independent linear instruction
bound for the actual halted invocation. Its word ranges, preloaded heap
representation and code/stack capacity are explicit. The
[realization loop rules](##Complexity.Computability.Ram.Compiler.Language.Realization.Loop)
reuse source termination without a second decreasing measure, and the
[ordinary-local cost rules](##Complexity.Computability.Ram.Compiler.Language.CostBound.Locals)
compose actual guard/body bounds and the source invariant. Their fixed-capture
rules reuse generated lexical preservation, leaving only mutable locals and the
heap in the author's invariant and potential. `StmtCostBound.while_contract_fixed`
and `RealizationWP.while_contract_fixed_of_total` consume the same independent
guard/body contracts. The library extracts their mathematical facts at the
actual execution points using `BlockSpec.post_of_eq`; authors do not reconstruct
operational observation equations. They supply the logical connection from a
true guard to the body's precondition, range evidence and numerical potential
inequalities. The source invariant and termination proof are reused. The
`BlockSpec.mono` consequence rule strengthens the input and weakens either
successful relation, while retaining the original precondition as a usable
fact. Mathematical invariants, frame composition and potential inequalities
remain explicit; correctness contracts themselves contain no instruction budget.

When an actual `Exec` is already available, `BlockSpec.post_of_exec` applies the
same contract directly at that execution's endpoint. Its input map may install
fixed captures or a local block's empty result slot; the result still observes
the complete actual final locals and heap. No client-side `Part` equation or
second execution witness is needed.

The [mathematical arena loop rule](##Ram.LanguageCompiler.StmtArenaCostBound.while_model)
reuses source guard and normal-body `BlockSpec` contracts at actual intermediate
heaps. The guard preserves the mathematical model, not necessarily the heap.
The fold cost proof uses its public
[mathematical round contracts](##Complexity.Language.List.Fold.Native), without
repeating execution transport; its program, signature and `remainingCost + 17`
bound are unchanged. Authors supply component bounds, an invariant and potential
inequalities; the rule bounds existing executions without another termination proof.

For finite ranges,
[`while_range_rel`](##Ram.LanguageCompiler.StmtArenaCostBound.while_range_rel)
reuses the source `guardRel`/`bodyRel` for normal rounds and direct function
returns. The body budget includes the whole actual iteration, including any
cursor increment executed. Local-pending completion instead uses
[`while_range_completion_rel`](##Ram.LanguageCompiler.StmtArenaCostBound.while_range_completion_rel):
the saved result leaves the body normally and exits through the real false guard.
The bound includes that guard's cost plus the normal-round and false-exit
overheads `10 + 11`, rather than treating the result as a function return.
For uniform guard and whole-body certificates,
[`while_range_completion_rel_linear`](##Ram.LanguageCompiler.StmtArenaCostBound.while_range_completion_rel_linear)
uses positive stride, `Std.Legacy.Range.size` and the existing `whileLinearBound`
to discharge the linear potential inequalities. The uniform guard certificate
covers both running and stopped paths; component bounds may be supplied by
`ram_source_arena_cost`. These are bounds on the actual loop, not complete
function RAM theorems; readiness and capacity remain separate obligations.
The existing allocating
[`prependRange` consumer](##Complexity.Language.Examples.LinkedList.NativeRange.prependRange_loop_costBound)
combines its generated round contracts with inferred guard/body bounds this way;
it supplies neither a second loop induction nor register-level proofs.
Eligible nonrecursive represented range sites expose `stateRel` and
`guard_rel`/`body_rel`, or their `_preserving` variants, under the actual source
loop. Correspondence reuses the relation and named proofs without regenerating
the body proof. Lean's closure retains captures, the initial heap, representation
premises and actual pending-slot conditions. The generated `Site.pending` names
the real slot for the running premise, without a handwritten lexical position.
Recursive and shared-continuation proofs remain local; eligibility is
conservative, including after value branches.
No new user syntax is required. These are low-level contracts whose closure
parameters still need a canonical consumer interface, not an automatic named
arena-cost entry.

`Buffer.Disjoint` permits different objects or disjoint `Set.Ico` intervals of
the same object. `Buffer.PreservesOutside xs initial finish` says that every
initially valid disjoint view retains its ordinary contents. Its `write`, `trans`
and `mono` rules derive and compose this fact from actual successful writes;
overlapping aliases remain allowed and observe their real updates. This is a
contents-preservation relation, not whole-heap equality or handle ownership.
The traversal's `boundedMap_total_frame` returns both the array-map result and
this frame at the same final heap. Its compiled `boundedMap_execute` exposes
that frame, the mathematical array result and the instruction bound against one
typed `FunctionExecution` outcome. The outcome retains the actual halted runner
and complete final machine memory; callers do not reconstruct the old witness
tuple. The two-call and imported clients use the corresponding
`boundedMapPair_execute` entry points. Neither array correctness nor
register-level simulation is proved again. The original `runUntil` theorems remain
available as lower-level compatibility interfaces.

## Recursive calls

For recursion, the [source contract rule](##Complexity.Language.Verification.Recursion)
`FunctionTotal.verify_wellFounded` supplies complete callable specifications at
smaller mathematical indices through Lean's `WellFounded.induction`. A fixed
function selector gives ordinary recursion; a varying selector supports mutually
recursive functions with different signatures. The index is mathematical proof
data, not runtime fuel, an instruction budget or a stack-depth bound.

The default represented frontend checks self-recursion from normal and
function-returning finite ranges using fixed captures or the actual range bound.
Shared [termination preprocessing](##Complexity.Language.Syntax.Termination)
uses Lean's `wf_preprocess` to expose `index < stop` to the author's decreasing
proof; both index-recursive consumers retain `decreasing_by omega`.
Generated correspondence reuses that proof at actual intermediate heaps.
Ordinary equations remain `foldl`/`forIn`, without attached proof arguments or
changed source control, heap effects or costs. The checked normal-range List
result uses ordinary induction and fold equations, not a second source proof.
General mixed local/function completion remains open, and no RAM cost bound is
inferred. Generated model equations may still require deliberate simplification;
unrestricted `simp_all` is not a guaranteed fast substitute.

For the supported pure fragment, the [named factorial](##Examples.Language.Factorial)
uses Lean's native termination machinery:

```lean
source_program (pure) Recursive where
  def factorial (n : Nat) : Nat := do
    if n == 0 then
      return 1
    else
      let previous ← factorial (n - 1)
      return n * previous
    termination_by n
    decreasing_by simp_wf; simp_all +zetaDelta; omega
```

The author supplies this decreasing argument once. Generated correspondence
reuses the native recursion principle to prove successful source execution with
the same result and unchanged initial heap, without a second implementation
induction. Ordinary `Nat` induction separately proves the mathematical equation
`Recursive.factorial n = Nat.factorial n`; the generated `_total` contract then
transfers that result to the actual source program.
The [compiled factorial](##Examples.Language.FactorialCompiled) reuses that same
source theorem. Its separate realization proof uses `ram_source_realize (input)`
with the recursive realizability and source contracts. It bounds intermediate
values by the representable factorial result and bounds nested calls by `n`;
parameter environments and statement-level target conversion are internal.
Its independent
cost induction uses `ram_source_cost (input)` and, in the successor case,
`ram_source_cost (input) using ih`, with actual generated call overhead. Argument
environments are opened internally; ordinary induction, recursive-input facts
and the final arithmetic inequality remain the author's proof.
The resulting halted-runner theorem returns factorial, preserves shared entry
memory and retains the generated code and stack-capacity premises. The linear
word-RAM instruction bound is in the numeric argument `n`, not its binary bit
length or the cost of arbitrary-precision multiplication. These backend range,
nesting and cost arguments do not repeat the source termination proof. Pure
mutually recursive families and a convenient named proof interface for effectful
recursion remain open; automatic pure correspondence is not a promise of
automatic termination transport for arbitrary effectful actions.
-/
