/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.Factorial
import Examples.Language.FactorialCompiled
import Examples.Language.LinkedList
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
native round proofs, as used by the scoped-allocation consumer. None of these
source rules asks for fuel or an instruction budget.

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

This interface describes normal rounds with justified preservation of captured
array observations. It needs no pure model of the complete loop, adds no source
helper calls and does not infer a RAM bound. General aliased in-place mutation,
effectful guard assignments and early/local-return rounds still use their source
contracts; they are not assigned an unproved pure transition.

## Finite ranges and resource rules

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

For a named local-return loop with an existing finite execution, use

```lean
ram_source_loop_arena (stateRel := invariantRelation)
  (prepared := bodyPrecondition) (completed := resultPostcondition)
```

The three relations concern visible source locals and actual heaps. This entry
selects the registered completion coordinates and execution frames, then applies
`ArenaReady.while_completion_of_exec`. Guard/body source contracts, their real
resource readiness, readiness of the final stopped guard, and the initial facts
remain obligations. The scoped-workspace consumer reuses its existing source
contracts here; it does not reconstruct private completion slots or prove loop
termination again. The rule preserves the same arena boundary between rounds,
not arbitrary growing allocation, and does not infer a time budget.

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
