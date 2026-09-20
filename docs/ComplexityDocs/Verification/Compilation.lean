/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.Buffer
import Examples.Language.BufferCompiled
import Examples.Language.Remainder
import Examples.Language.Scalar
import Examples.Language.ScalarCompiled
import Examples.Language.ScopeCompiled
import Examples.Language.TraversalCompiled
import Examples.Language.TraversalCompositionCompiled

/-!
# Connecting source proofs to RAM

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Finite-word realization

The [compiled buffer invocation](##Examples.Language.BufferCompiled) reuses its
[source contract](##Examples.Language.Buffer) and derives the read cell's range
from the input heap representation.
Its separate bound concerns the same read/helper/write/slice program and its
actual returned descriptor and updated heap. Borrowed aliases remain allowed;
the example does not establish a general mutable-loop proof interface.

The [scalar example](##Examples.Language.Scalar) calls a real increment helper,
assigns a local in the selected branch, then proves its returned value equals `min (n + 1) limit`
using ordinary Nat facts. Its `increment_eq` and `boundedIncrement_eq` proofs
reason about native values; the latter unfolds its definition, simplifies
`Id.run` and `Id.instMonad`, reuses the helper result and splits the mathematical
comparison. Rewriting the generated `P.f_total` contract with these equalities
supplies the source contract required by compilation, without a second
implementation induction. Default effectful declarations retain `P.f_total_iff`
for ordinary curried preconditions and actual initial/final heaps.
Direct source-WP rules remain available when a
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

## Simulation and actual instruction counts

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
the callee body and frame, without a user-supplied ABI price. `callCost_eq_add`
separates the body count from the fixed generated overhead, so a recursive bound
can use ordinary arithmetic without unfolding frame or return layouts.
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

## Publish a typed execution result

The [typed execution interface](##Complexity.Computability.Ram.Compiler.Language.FunctionExecution)
publishes the result without rebuilding that runner tuple for every example.
`FunctionCapacity` contains the existing positive-width, code and stack
conditions; `FunctionLaunch` adds the actual argument ranges and represented
starting memory. Neither contains the algorithm's correctness predicate or a
proposed time bound. `FunctionRealizable.execute` composes source correctness
and realizability; `execute_le` adds a separately proved instruction bound.
Its `FunctionExecution` result retains actual source evaluation, returned words,
halted runner state, body time and complete step count. `nextEntry` carries the
entire returned physical memory into a later invocation. The factorial and
splay consumers use the same interface, including factorial's preservation of
arbitrary initial RAM memory below the heap boundary.

For allocation and reclamation, the corresponding
[arena execution interface](##Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution)
uses `FunctionArenaLaunch` and `FunctionArenaExecution`. It additionally retains
the actual final placement and cursor, rooted inputs and a measured invocation
at the specified call depth. `ArenaReady.execute` needs no time budget;
`FunctionArenaRealizable.execute` adds the independent source specification.
Its `memory` is an `ArenaRep` on the actual halted machine, and `nextEntry` keeps
that complete memory for a later call. The
[scratch client's](##Examples.Language.ScopeCompiled) public theorem now states
only mathematical contents, final cursor and the actual workspace conclusion.
The runner, return-field and representation facts come from this shared result.
The workspace rules bound all actual accesses and out-of-envelope writes at
every prefix; they do not claim an exact reachable-live-space count.

## Compose independent time bounds

Use the [structural bound rules](##Complexity.Computability.Ram.Compiler.Language.CostBound)
to compose source costs. `StmtCostBound` bounds the existing execution observation;
its primitive, sequence, branch, return and call rules hide case analysis on
`ExecutionCost`. `FunctionCostBound.of_stmt` adds the returning-body wrapper once.
`ram_source_cost (n limit) using increment_costBound` applies these rules to the
scalar consumer and compares the inferred bound with its requested bound.
For several callees, `using [recursiveBound, rotateRightBound, rotateLeftBound]`
selects among the supplied contracts at the actual call. Their own preconditions
remain proof obligations; the author need not construct a dependent function
table. `ram_source_cost_intro (names)` opens only the function-body rule and
ordinary parameters, leaving mathematical case analysis before the structural
pass. It expects the existing body wrapper's `core + 2` bound shape.
Its uniform bound needs no proof of the minimum;
result-dependent bounds can reuse an existing source contract through the call
rule. A guard proved from source values and local facts selects only its actual
branch through `StmtCostBound.ite_true` or `ite_false`. If neither decision can
be proved, the tactic retains the uniform maximum of both branches. The default
call form infers a uniform numerical continuation bound. A uniform bound may
still need a callee's postcondition to establish a later call's input.
Neither instruction prices nor mathematical correctness proofs are duplicated.

The [compiled traversal](##Examples.Language.TraversalCompiled) also lets the
solver infer uniform budgets instead of copying numeric constants. `guardCost`
and `bodyCost` pair one natural-number witness with a proof for every local
environment and heap; the witness is introduced before those quantified values.
`ram_source_cost_step` determines it from the actual source structure and supplied
callee certificates. `ram_source_cost_intro` similarly infers the function wrapper
around the supplied loop bound. Direct, two-call and imported clients reuse the
resulting `boundedMapBodyBound` rather than repeat its expression.
`StmtCostBound.whileLinearBound` includes the normal-loop and false-exit charges;
its lemmas leave the remaining-iterations inequality to the author. This does not
discover invariants, nonlinear recurrences or dependent numerical bounds.

For a numerical bound depending on the actual result and final heap, provide
the ordinary bound function explicitly:

```lean
ram_source_call (next := fun (value : Nat) finish => remainingBound value finish)
  using callee_cost, callee_total
```

The command leaves the continuation's cost proof and the final numerical
comparison under the supplied callee postcondition. It reuses
`StmtCostBound.call_of_spec_le` or `call_seq`, according to the actual source
statement; no hypothetical returned value or unchanged-heap premise is added.
The scalar consumer uses the returned increment to select different branch
bounds. The two-buffer consumer separately demonstrates transport of the actual
final heap and its frame facts. An author still supplies the mathematical bound;
the command does not infer arbitrary result-dependent recurrences.

`StmtCostBound.call_seq` handles a standalone call followed by another statement.
It reuses the supplied callee contract to pass the actual final heap and ordinary
postcondition to the next bound, keeping caller-local restoration and empty
result-scope cases inside the shared proof. The
[compiled two-buffer composition](##Examples.Language.TraversalCompositionCompiled)
uses its uniform specialization twice and reuses the original traversal's bounds.
Its actual halted invocation retains both arrays and the outside-both frame in
the same represented final heap. Word ranges, code capacity and space for
pair/traversal/helper remain explicit; these are not a proposed instruction budget.

For such composition, start with `ram_source_cost (xs ys limit)` without `using`.
The structural pass opens ordinary parameters and stops at the first call.
On that call goal, select its contracts explicitly:

```lean
ram_source_call using (boundedMap_costBound leftContents),
  (boundedMap_total_frame leftContents)
```

This handles one call, retaining its actual result, final heap and postcondition,
then stops at the next call. In the two-buffer proof, the first frame establishes
that the second input still has `rightContents`; the next `ram_source_call` uses
the corresponding right-side contracts. The full proof, including input facts
and the final arithmetic inequality, is `boundedMapPair_costBound` in the linked
example. After the calls have fixed the inferred bound, `ram_source_cost_step`
simplifies its generated constants in the remaining inequality; ordinary
arithmetic proves the requested budget. Argument packing, scope restoration and
intermediate structural bounds are inferred by shared rules. The same command works after `ram_source_realize`,
with a realizability contract in place of the cost contract.
Contracts are never invented or searched for globally. Multiple explicitly
supplied contracts are matched against the actual callee; the original single
`using` mode reuses its supplied contract throughout the pass. Loops remain explicit proof
boundaries in either mode, and neither mode invents an invariant or a frame fact.

For typed loops, `StmtCostBound.while` uses a state-dependent potential. The
guard and body bounds follow the actual state; normal iterations account for
the remaining potential, while false exits and early returns discharge their
own remaining work. The final false guard is counted. This is a conditional
cost rule for the same execution, separate from the well-founded termination
rule; the structural tactic does not yet choose or apply loop invariants.

## Supported boundaries

The frontend supports `Nat`, `Bool`, `Unit`, borrowed buffers, products, options,
lexical bindings, actual named calls, branches and returns. Nested addition, multiplication, saturating
subtraction, division, remainder and comparisons are normalized left to right
into actual primitive bindings. This also applies to guards and call arguments.
The [remainder example](##Examples.Language.Remainder) implements
`n - (n / d) * d`, reuses the ordinary Nat identity, and derives the actual
compiled result with a separate instruction bound. Divisor zero is included;
no artificial subtraction-order condition is required.
Named effectful `while`, bounded `for`, option matching and initialized allocation are supported as
described in the [loop guide](ComplexityDocs/Verification/Loops.html).
Product/option construction, projection and local assignment
are covered by the same structural realization and cost tactics. General sums,
recursive data representations, general pure `while`, mutually recursive pure families and richer
callee selection, recursive proofs and data-dependent bound automation remain
unfinished. Costs are currently derived
for successfully realized executions, not an instrumentation theorem for
every unrestricted source execution.
The checked fragment does not establish the complete source proof and
specification interface needed by general mutable collections and recursion.
Optimizing code size does not imply every execution is faster.
The [direct word-RAM workflow](ComplexityDocs/GettingStarted/WordRam.html) and the
maintainer interfaces below remain available.

## Compiler-maintainer interfaces

Compiler maintenance is a separate, active proof workflow. The
[layout rules](##Complexity.Computability.Ram.Compiler.Language.Layout),
[return-flag preservation](##Complexity.Computability.Ram.Compiler.Language.Control)
and measured simulation compose actual register updates and calling conventions.
The same layout indexes every actual value field. Parameter packing and fresh
receivers use those indices and the existing register-update rules; Unit has no
dummy field. Buffers have two fields, their actual base address and length;
products concatenate component fields and options add a tag before their payload.
Absent payload fields are zero padding, not a manufactured buffer. Selected
payload copying is real emitted work, included in the exact instruction count.
Sequential multi-field copies preserve
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
-/
