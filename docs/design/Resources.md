# Cost analysis and complete claims

Resource bounds concern the same declared implementation and actual execution as
its behavior theorem. Uniform problem claims additionally fix encoding, widths and domains.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Separate cost, over the same core execution

Define a cost observation of the same typed core, parameterized internally by
a proved backend interpretation. It is not a second user program or a
source-visible budget. Require:

- erasure: forgetting cost yields exactly the source execution;
- instrumentation: each source execution admits that cost observation;
- determinism: the chosen interpretation fixes the count for that execution,
  independently of proof terms used to establish execution or termination;
- noninterference: source branch selection, effects and termination do not
  inspect the count or the proposed bound.

These are the intended interface obligations. Current `ExecutionCost` is
indexed by successful `RealizedExec`, and every such execution admits a count;
this is not yet instrumentation of every unrestricted source execution.
Conditional `FunctionCostBound` alone can be vacuous when execution is not
realizable. Publication must continue to combine independently established
source totality, realizability and the bound, as the existing runner bridge does.

The RAM interpretation comes from the actual lowering/layout. Its charges
include operand evaluation, copies, descriptor fields, guard/jumps, traversal
setup/load/update, argument preparation, callee frames, return fields, receiver
updates for calls inside the body. A source call does not have a
layout-independent exact constant. Ghost mathematics is erased; actual runtime
work is not.

Use one accounting convention: `sourceCharge` covers the selected lowered
function body and all complete internal calls. This includes the body's private
flag initialization, as well as checks crossed after an early return. Complete
functions omit the empty final dispatch; a generic wrapper with a normal
continuation still charges its actual dispatch. `outerOverhead` covers only the external entry trampoline,
outermost calling convention and final halt. No instruction belongs to both.

The upper-bound connection must have the useful direction:

```text
actualTargetSteps <= sourceCharge artifact sourceExecution + outerOverhead artifact
```

Exact equality is useful for some fragments, not required for every
optimization or upper bound. The source charge and outer overhead are proved
from emitted code; user-selected operation prices or unchecked ticks do not
establish a RAM bound.

The initial publication theorem combines source total correctness, realizability
and a bound on that same source execution. Forward finite-execution simulation
with a cost bound, followed by target determinism, suffices to identify and bound
the actual runner. It does NOT by itself supply an unconditional converse for
every completed target trace. A conditional target-bound API without source
termination additionally requires completed-trace reflection or an equivalent
adequacy theorem; keep that as a distinct obligation.

Cost composition follows actual returned values and updated data in execution
order. Use a shape/length/frame consequence of a behavioral contract when that
is all a bound needs; retain content facts when the work depends on them.
Do not repeat sorted-content reconstruction merely to recover lengths, and do
not remove premises from existing time contracts without proving replacements.

Use mathlib sums, asymptotics and recurrence results, plus the existing potential
lemmas. Generating structural cost obligations does not automatically discover
the right recurrence, potential or invariant. Ordinary behavioral equality
allows mathematical reuse but never transfers an algorithm's cost by itself.

The current [structural scalar rules](../../Complexity/Computability/Ram/Compiler/Language/CostBound.lean)
expose `StmtCostBound` for a source statement and its entry values. This is a
conditional upper bound on the existing `ExecutionCost` observation, not a new
interpreter or termination proof. Rules compose primitives, returns, sequencing,
the selected branch and actual calls without making consumers destruct the
execution relation. `FunctionCostBound.of_stmt` adds the returning-body wrapper
once; `callCost` still comes from the actual calling convention. The proved
`callCost_eq_add` separates the body count from that fixed generated overhead,
keeping frame and return layouts out of recursive arithmetic proofs.

The scalar consumer now uses `ram_source_cost` to compose these rules. Its uniform branch bound
does not need the helper's mathematical result; a result-dependent continuation
can instead reuse a consequence of an existing source contract through the call
rule. Structural rule selection and intermediate bounds are generated from
the existing theorems; ordinary arithmetic tactics finish the requested
inequality. When the guard follows from source values and local facts, the
tactic selects only that branch through the proved `ite_true`/`ite_false` rules.
Otherwise it retains a uniform maximum; it does not guess a symbolic decision.
By default the tactic uses a uniform continuation bound; this does not require
an unchanged heap or discard the callee's result properties. Named
`ram_source_call (next := fun value heap => ...) using resource, specification`
also exposes the general result/state-dependent numerical rule. The author
supplies the numerical function, while the shared rule retains the actual
callee result and postcondition. `StmtCostBound.call_of_spec` and `call_seq_uniform` retain
the supplied source postcondition while inferring the continuation's uniform
bound. The latter specializes `call_seq`, which hides standalone call/skip
execution cases and charges the actual normal sequence dispatch.

For effectful composition, `ram_source_cost (xs ys limit)` stops before the
first call. `ram_source_call using resource, specification` applies one selected
cost contract and source contract, then continues structurally until the next
call. The two-buffer composition uses this interface twice, with separate
contracts for the two mathematical contents. It no longer opens argument
environments, restores result scopes or supplies intermediate structural bounds
by hand. Its actual intermediate-heap frame argument and final cost inequality
remain explicit. Contract selection is not automatic; the existing single
`using` mode still reuses its supplied contract throughout the structural pass.

Uniform structural budgets can be inferred rather than restated as numeric
constants. The traversal keeps a natural-number witness together with its
`StmtCostBound` proof; `ram_source_cost_step` fixes that witness by applying the
existing compiler-derived rules. The witness is introduced before arbitrary
locals and heaps, so it cannot silently depend on a particular observed state.
The same method uses `ram_source_cost_intro` to infer the complete function
wrapper around a supplied loop or callee bound. Direct, two-call and imported
clients refer to the resulting named bound rather than copy its expression.

`StmtCostBound.whileLinearBound` supplies the existing loop rule's structural
charges for a uniform guard/body budget. Its exit and step lemmas leave the
author the mathematical remaining-iterations decrease; early return retains
its separate obligation. This does not infer a loop invariant, discover a
nonlinear recurrence, or force a state-dependent bound to be uniform. Those
cases continue to use the general potential and dependent-call rules.

The function-exit optimization separately removes the redundant final dispatch.
The actual body is three instructions shorter, its inferred register bound is
unchanged, and measured lowering charges initialization plus the core (`+2`).
The generic statement wrapper and its returning-path `+5` are unchanged.

## Source-level complexity milestone

**Status:** compiler-derived step counts and independent conditional bounds
exist. The shared `FunctionCapacity`/`FunctionLaunch` and `FunctionExecution`
interfaces now separate admissible preloaded inputs from the actual typed
runner result. Factorial and splay use the same `execute_le` rule; neither
reconstructs the old runner witness tuple. Named calls accept an explicit
result/heap-dependent continuation bound; the scalar consumer checks a
returned-value-sensitive bound, and traversal checks actual heap/frame transport.
`FunctionArenaLaunch` and `FunctionArenaExecution` provide the corresponding
allocation-aware result: actual final placement/cursor and complete machine memory,
with the known call depth retained. The scoped-workspace consumer now uses this
shared result and its actual access-set bounds instead of assembling a large
runner tuple. Concise loop-resource interfaces, further consumer migration,
general live-space observations and problem-level composition remain unfinished.

Local-return loops can lift the same finite source execution through
`ArenaReady.while_completion_of_exec`. It consumes their visible guard/body
contracts and generated completion frames, internally distinguishing continuing
and completed rounds. The scoped-workspace consumer no longer reconstructs that
invariant or converts its source contracts through `Part` result equations.
Word ranges, actual callee nesting and scratch capacity remain resource
obligations. This rule keeps the arena boundary fixed across rounds; growing
allocation and general live-space composition still require separate interfaces.
`while_completion_model_of_exec` reuses the mathematical guard/body contracts
and their invariant through this same rule. Its named-loop entry
`ram_source_loop_arena_model` selects checked coordinates and frames; proved
identity correspondence can remove entry tuple transport. It does not require
or infer an inverse for general heap-indexed representations. The author still
supplies actual word ranges, call nesting, scratch capacity and saved-result
readiness, but does not reconstruct source preservation in the resource proof.

`ArenaReady.call_seq_of_exec` composes a standalone call with its next statement
on the same finite execution. The next statement sees the callee's actual final
heap and restored caller locals; initial, callee-final and final arena cursors
may differ. The named fragment entry `ram_source_fragment_arena_call` uses this
rule for a fixed-placement continuation, normalizing argument ranges and source
coordinates before the existing realization pass. The scoped consumer supplies
its worker certificate without destructing call/sequence executions or building
argument environments. Allocating continuations remain explicit uses of the
general rule; neither interface supplies a time bound.

Uniform structural budgets are inferred through the existing checked cost rules.
Traversal's guard/body witnesses are chosen before arbitrary locals and heaps,
and its function wrapper is inferred around the supplied loop bound. Direct,
two-call and imported clients reuse the named bounds instead of copied constants.
`whileLinearBound` supplies structural loop charges; the author still supplies
the iteration measure, potential inequalities and any data-dependent recurrence.
This is neither a new operation-price table nor automatic complexity analysis.

Pure finite ranges can reuse their generated guard/body correspondence directly:
`while_range_encoded` supplies the exact native range-count descent internally,
including empty ranges, positive dynamic stride and early function return.
The structure-valued `StructuredRange.sum` consumer infers its complete function
bound around that rule. Uniform component bounds remain proved compiler
budgets, not assumed prices for native mathematical operations. General
data-dependent loop bounds still need the author's invariant or potential.

**Array-task integration:** the shared
[`ArrayFunction`](../../Complexity/Language/ArrayFunction.lean) interface selects one
declared `Buffer Nat → Nat` source function. `Correct valid answer` states ordinary
`Array Nat` input/output correctness and successful termination without resources;
the [RAM `TimeO` interface](../../Complexity/Computability/Ram/Compiler/Language/ArrayFunction.lean)
uses that same implementation and the existing allocation-aware execution result.
It fixes input layout and a logarithmic input-width scale, permits one uniform
constant width factor, and requires actual executions for every legal input at
every admitted width. Capacity is proved for those executions, not a premise
that silently excludes inputs. Its bound uses mathlib `IsBigO`.
This is a preloaded single-array/natural-result interface, not general I/O,
input loading, a persistent pure container API or a replacement cost semantics.
The interface and actual RAM connection are checked; existing clients can reuse
them through the fixed-type program wrapper below.

**Fixed-type program wrapper — checked:** `Complexity.Program Input Output`
selects the same typed source function with externally fixed input and output
representations. `Correct valid post` accepts an ordinary mathematical relation;
`TimeO valid size growth` keeps the task's size measure explicit and uses the
existing actual RAM execution. The source wrapper, scalar and multiple-array
inputs, structural outputs and compatibility with `ArrayFunction` are checked.
The [typed-program consumer](../../Examples/Language/Program.lean)
publishes an existing two-argument source function using its generated total
contract and ordinary mathematical equation. `Correct.of_functionTotal` supplies
the shared invocation bridge, without a second algorithm or environment adapter.
Registration must be fixed by the interface, not supplied by a candidate as free
preprocessing or answer decoding. Right-associated natural/Boolean array and
scalar inputs now compose in a shared layout: arrays append objects to the
existing heap, while scalars only prepend arguments. Old identities and contents
remain unchanged. The opt-in `Input.PrefixClosed` property
records exactly the preservation needed for composition; arbitrary custom input
relations are not silently assumed to have it. Physical initialization reuses
the same generic `ArenaRep.push_buffer` theorem as actual runtime allocation.

Standard `deriving Program.Input, Program.RamInput` and `deriving Program.Output`
register closed records through one checked direct-field embedding. The append
consumer now declares a native function directly on two array fields and returns
an array-valued record: `{ values := input.left ++ input.right }`. Field reads,
record construction and the real allocating append call are elaborated together
with checked native/source correspondence. Preservation of old array observations
comes from the copy implementation's contents frame, not merely heap shape.

`program% NativeAppend.append` selects that actual generated source. Its shared
`Packing` entry assembles the fixed separate input parameters using real product
primitives before calling the native function's source body. `program_correct`
combines its registered correspondence with an ordinary mathematical equation;
the consumer needs no private heap or source-environment adapter. Output
compatibility checks the complete representation, not just the core value type.

The supported ordered field tuple must already have a layout. Native selection
currently requires one mathematical parameter. Parameterized/dependent/inherited
records, arbitrary source datatypes and a complete persistent array operation
library are not covered. Natural-array append is connected; this does not claim
all Lean array operations.

**Native record append through complete RAM time — checked:** the
[compiled consumer](../../Examples/Language/ProgramCompiled.lean) proves linear
`Program.TimeO` in the sum of its two input lengths for that same high-level
program. The source-copy loop contracts supply the existing invariant and
termination reasoning. Independent arena cost rules account for actual output
initialization and both copies. Shared `Uncurry` and `Packing` rules add the
generated field projections, entry assembly, calls and returns; the time
publication rule adds the actual outer invocation and halt. The packing used
in the proof is read from the generated program, not separately reconstructed.

One input-independent width constant establishes code and fixed-depth stack
capacity, while the input's extra bit provides room for the output and exact
cell values. The theorem quantifies over all input arrays and every admitted
width; capacity is not a mathematical input precondition. Its asymptotic relation
is mathlib's `IsBigO`. Resource-certificate composition is still explicit in the
compiled consumer; generating these structural combinations for general native
programs remains an automation task, not a missing execution or cost connection.

Keep three layers distinct: mathematical behavior; resource arguments over the
same source implementation; and a concrete backend adequacy theorem. Ordinary
function equality belongs to the first, not a way to recover the other two.
Further source-level resource inference is follow-up work here, not an open-ended
condition on the allocation foundation. Author-supplied mathematical ranges,
capacity and invariants are part of the proof, not missing compiler automation.

1. Expose proved operation/callee bounds at named functions and source arguments.
   Hide `lowerFunc`, function-table indices, register layout and ABI formulas
   in shared rules. Support actual result/state-dependent continuations using
   the existing general cost rules, not another interpreter or pricing table.
2. Generate the final typed execution theorem from behavior, realizability and
   resource contracts. Authors should not reconstruct the runner's large
   witness tuple, argument encoding or output decoding for each program.
   Remaining conditions must be meaningful source ranges and storage bounds.
   Preserve the algorithm's own precondition as well as representation and
   capacity assumptions. Domain-restricted total interfaces should use explicit
   domain arguments or an implemented error result, not an arbitrary default
   value extracted from a partial computation.
3. Reuse mathlib `IsBigO`, sums and recurrence results and the library's existing
   potential/composition tools. Derived asymptotic interfaces should hide exact
   implementation constants without hiding actual work or the admitted domain.
   Finish the shared array-task consumer and connect the existing
   [uniform time](../../Complexity/Computability/Ram/Time/Basic.lean)
   and [problem certificates](../../Complexity/Computability/Ram/Problem/Basic.lean)
   to the high-level declaration rather than creating another certificate system.
4. State the model early: current bounds count word-RAM instructions, including
   unit-cost word multiplication/division. They are not bit-operation bounds.
   Fix input encoding/size, legal inputs, width policy, one implementation family
   and the loading/output convention before publishing problem complexity.
   Current uniform certificates fix one emitted `Code` across inputs and widths;
   a more general width-dependent artifact family needs its own certificate bridge.
5. Distinguish stack/address capacity, occupied/reserved heap, cumulative
   allocation and peak live storage. Reuse existing
   [prefix/peak resource tools](../../Complexity/Computability/Ram/Execution/Resource.lean),
   but provide an observation and lifetime connection for each new resource.
   A renamed capacity premise or cumulative access set is not live space.

**Advance when:** an algorithm author derives a mathematical complexity claim
and a typed execution guarantee for the same declaration without opening ABI
definitions. For an unbounded input family, the width/storage policy and cost
model must make the quantified statement meaningful. The current factorial's
linear word-step bound in numeric `n` is useful evidence, not a claim of linear
bit complexity or arbitrary-precision multiplication in constant time.
