/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session
import Complexity.Language.Session.Refinement
import Complexity.Language.Session.Prepared
import Complexity.Program.SumOutput
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Computability.Ram.Compiler.Language.Session.Induction
import Complexity.Computability.Ram.Compiler.Language.List.Prepare
import Complexity.Computability.Ram.Compiler.Language.Buffer.Prepare
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.TraceTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.ScheduledTraceTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.PhaseTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.PreparedTraceTimeBound
import Complexity.Computability.Ram.Compiler.Language.Session.PreparedHistoryTimeBound
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Buffer

/-!
# Persistent sessions

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

A closed `Program` starts from its input representation on each invocation. An
online service instead initializes once and keeps the state and heap returned by
each call. Reconstructing that private state from mathematical contents would
describe a different computation.

## Source meaning

`Complexity.Language.Session` selects two entries of one existing source program:

- initialization receives only the declared configuration and returns a state;
- a step receives that actual state and the current request, and returns a reply
  paired with the next state.

The implementation chooses its source state type. Configuration, request and
reply types are fixed by the client. This typed connection interface does not
introduce a second evaluator, a host callback, or a new language construct.

`Session.Starts` and `Session.Step` are equations for the selected entries'
existing source evaluation. `Session.Run` composes steps through their actual
intermediate states and heaps; `Session.Runs` includes initialization, even for
an empty request list. A request list in these propositions is environment proof
data, not an argument passed to either source entry.

The caller supplies the initial heap and configuration. A protocol that allows
only public scalar configuration should fix an empty initial heap and expose
only those scalars; the generic session type does not establish this boundary
on the caller's behalf. The same applies to request loading: reference-bearing
external inputs need a justified loading and memory protocol.

## Correctness proofs

Prove an initialization contract and a step contract for an invariant about the
actual state value and heap. `Session.Run.exists_of_step` composes a total step
contract over any finite list of admissible requests, without a time budget.
`Session.Run.append` joins traces at their actual intermediate heap, and
`Session.Run.length` gives one reply per successful request.

For an ordinary mathematical transition `step : State → Request → Reply × State`,
`Session.StepRefines` relates its state to the actual source value and heap. Prove
one step using that relation and the reply's existing `Representation`.
`StepRefines.runs` then relates the complete source history to `Session.modelRun`,
which is Lean's left-to-right `List.mapM` in `StateM`, used only as a proof model.
Neither the model state nor the future request list becomes a source argument.
The state relation can retain ghost invariants without requiring a unique runtime
encoding of mathematical state.

`Session.ValidInputs` checks admissibility at each mathematical state. A protocol
with a bounded number of requests can retain the remaining count as a ghost;
its contract need not promise another successful step after completion.
`StepRefines.post_of_runs` gives the same observations for an already supplied
actual trace. In particular, use the source projection of a RAM trace to attach
correctness to that very computation, not a separately selected witness.

Replies are paired with their own return-time heap, so mathematical observations
can use the contents that existed when the reply was produced. These proof-level
heaps do not copy or freeze runtime storage. A returned reference may still
alias storage changed by a later request; persistent contents require a separate
ownership or frame argument.

Faults and divergence do not satisfy the successful-run relation. Successful
correctness and termination remain independent of machine width or a proposed
resource allowance.

## RAM realization and costs

`Ram.LanguageCompiler.Session.State` retains the actual heap, placement, cursor
and complete RAM data projection. Its `ofExecution` constructor uses an existing
`FunctionArenaExecution`; it does not bootstrap the arena again.

The RAM `Run` relation chains those actual executions of the same source
entries. Its `source` theorem recovers the independent source relation.
`init_next_words` and `step_next_words` show that the next call's state fields
are the preceding invocation's actual returned words. Only the current request
is appended; no mathematical private-state loader is introduced.

The cost index sums the actual complete preloaded invocation counts.
`Run.append` adds these counts while retaining the real boundary memory.
Each invocation still needs the existing word-range, heap, stack and readiness
conditions; source totality alone does not supply finite machine capacity.

`Run.exists_le_of_step` composes a supplied invariant and per-request invocation
bound over a finite history. Each step premise must produce a real execution,
preserve the invariant at `State.ofExecution`, and bound that execution's count.
`Runs.exists_le_of_step` includes an actual initializer and its instruction count,
even for an empty history. This gives the initializer's count plus the sum of the
request bounds, without repeating the trace induction in each consumer.
These resource rules currently use a fixed admissible-request domain and an
invariant closed under all those requests. They do not infer that a finite
protocol continues to accept requests after its terminal state.

## Preparing current heap-backed inputs

Heap-backed feedback cannot be supplied by a pure request encoder: its nodes
must exist in the current memory. `Ram.LanguageCompiler.List.Prepare.Run`
records real compiled `List.Cons` invocations from a retained `Session.State`.
The tail is prepared before the head, preserving input order and allowing an
existing linked suffix to be shared. Every intermediate world comes directly
from `State.ofExecution`, not a freshly initialized heap.

`Prepare.exists_le` constructs this preparation from scalar word ranges and
capacity. It allocates exactly three words per new node and bounds the actual
invocation sum by the input length times the existing compiled constructor
bound. `Run.observed` retains the complete old object prefix and placements,
so existing arrays, aliases and linked roots remain valid. `Run.retained_words`
preserves the encoding of any old rooted state value.

The source `List.Prepare.Run` records the same constructor calls without a RAM
budget; `exists_run` establishes their totality. RAM `Run.source` projects the
actual preparation to that source relation.

`Session.PreparedRun` interleaves a protocol-fixed current preparation with the
selected step, retaining the state value and using the preparation's actual
final heap. Its RAM counterpart uses the corresponding physical memory and
adds preparation and callback invocation counts. Prepared arguments must fit
that machine. `PreparedRuns` includes the one actual initializer, and source
erasure retains every intermediate heap and return-time reply.

For ordinary mathematical transitions, `PreparedStepRefines` proves the step
after each actual preparation. The state relation must be transported using
the concrete preparation's frame; arbitrary invariants do not survive heap
extension automatically. Its `run` and `runs` theorems reuse `modelRun` and
source preparation totality, without a resource premise.

`PreparedTraceTimeO` and `PreparedTraceTimeOOn` constrain the same accepted
prepared RAM trace, using public configuration width and global mathlib bounds.
The client fixes the preparation relation and must back its prices with actual
executions, such as `List.Prepare.Run`; a candidate-selected annotation or
arbitrary relation is not a loader implementation. The concrete source
correspondence also projects this accepted trace to source.

Ordinary `Session.Run` still has no intervening allocation and is unchanged.
External traversal, scalar loading, transport and driver control remain outside
these preloaded calls. Placement stability does not implement saving old state
registers across constructor calls. The native host input loaders are a
separate backend boundary.

For natural arrays, `Buffer.Prepare.Run` uses the existing initialized buffer
allocator followed by one real scalar-write invocation per cell. Its source
relation is total for every finite array, including an empty array. The RAM
relation threads the complete actual memory through allocation and every write;
its `source` projection retains that same preparation. `Run.observed` gives the
original ordinary array and preserves exact old objects and their placements.
Consequently a later input can be loaded without reconstructing private state
or invalidating contents of previously retained views.

The actual preparation count is affine in the current array length. It includes
initialized allocation, every scalar write and their invocation wrappers.
`exists_le` constructs the executions from word ranges and available arena
space. These are helper assumptions for realization, not additional legality
conditions that a task may silently impose on its inputs. Array traversal and
transport into the scalar ports remain external, just as for linked inputs.

`PreparedHistoryTimeO` and `PreparedHistoryTimeOOn` combine this preparation
boundary with the finite raw-request `historyWidth` policy. They are useful
when initialization has no size-bearing configuration but subsequent external
requests contain arbitrarily large current arrays or integers. The protocol
fixes the preparation, raw admission words, legal histories, reply property and
growth expression. Only the declared configuration enters the initial memory;
each request is prepared at its own call boundary. The bound covers one actual
initialized RAM history, including all preparations and callbacks, and its
postcondition observes the replies of that very history. The `source` theorem
projects the same accepted execution without imposing a source-level budget.

This is a total-history bound: it allows initialization or cleanup charges to
be amortized across calls. Use the phase interface below when each callback
needs its own latency bound. Fixed external histories are not adaptive games,
and neither prepared interface supplies a continuously running I/O driver.

## Uniform callback-time requirements

`Session.TimeO` and `Session.TimeOOn` use the existing fixed `Program.Input` and
`RamInput` configuration layout. `State.ofInput` constructs its represented
starting memory before initialization; neither the candidate nor the future
request history chooses that memory. The global width multiplier and ordinary
mathlib `IsBigO` envelope follow `Program.TimeO`.

For every legal history and every configuration-admitted width, the requirement
asks for current-request word-range proofs and actual initialized RAM invocations
within the envelope. Code, stack and allocation facts are obligations of those
executions; none of these facts is an extra task precondition. In this interface
the configuration fixes the width
scale, so requests must fit that policy; an unbounded stream of arbitrary new
integers or heap-backed external inputs needs a different input protocol.

The fixed request encoder presents only the current public ports. The history
and the mathematical size expression are proof data, not source arguments.
Independent source correctness applies to the same costed trace: `Runs.source`
projects that trace, and source `Runs.deterministic` aligns it with any successful
source witness. An executable streaming adapter is not needed to state this
preloaded-callback requirement; it is needed for a separate runtime/I/O claim.

## Separate initialization and request bounds

Some protocols admit arbitrarily large scalar requests after a fixed
configuration. `Session.historyWidth` extends the usual logarithmic scale with
the fixed raw request words. This is a finite-history machine-admission policy,
not a source input or preprocessing step. At a fixed configuration and width,
`ofInput_history_independent` proves that the complete initial memory is identical
for different histories. The source cannot inspect the width policy, and the
requirement covers every sufficiently large width. This does not implement an
infinite stream with dynamically growing words or load external heap references.

`Session.PhaseTimeO` has independent global envelopes for initialization and each
request. `PhaseTimeOOn` accepts their mathematical growth expressions directly:
for example, a setup expression depending on the configuration size and a
constant request expression. A constant expression gives one global latency
bound, independent of configuration, request values, history and width. A bound
only on the complete history would not prevent expensive deferred setup in the
first callback.

The underlying RAM `BoundedRun` retains each real invocation and its individual
bound; `BoundedRuns` separately bounds its actual initializer. Their `run` and
`runs` erasures preserve the existing unbounded trace and exact step count.
Their `steps_le` lemmas recover the summed bound without exchanging budget
between phases. As with `TimeO`, request fitting, capacity and termination are
conclusions for every legal history. The fixed raw-word presentation is chosen
by the protocol author and must not encode answers or candidate-selected padding.

## Feedback determined by actual replies

For a closed-loop protocol, a legal next request can depend on the preceding
reply. `Session.TraceTimeO` and `TraceTimeOOn` bind a fixed acceptance predicate
to the requests and actual return-time replies of the same costed RAM trace.
The predicate can require current-state feedback, valid actions and stopping
at the first successful terminal state. It must describe those rules explicitly;
an arbitrary externally supplied feedback list is not a closed loop.

The environment type may depend on the public configuration. Each legal hidden
initial environment is quantified independently, but it is never an input to the
source initializer or to the word-width policy. Only the public configuration
creates the initial memory. Request fitting and real executions remain
conclusions at every admitted width. `TraceTimeO.source` projects that very RAM
trace to source, preserving its acceptance evidence.

This is an accepted-trace requirement, not another evaluator or a price for the
judge's computation. For a fixed deterministic environment, causal acceptance
can describe the complete interaction. Existence of one accepted trace is not
a guarantee against every choice of a nondeterministic or adaptive adversary.
Keep an independent source-correctness proposition using the same protocol;
the compiled-time bound and an executable streaming adapter are separate work.

## Later public announcements

A long-lived process can start before the sizes of its later jobs are announced.
For such a process, an empty initial configuration cannot determine enough word
space for all future jobs. `ScheduledTraceTimeO` and `ScheduledTraceTimeOOn`
combine the existing finite `historyWidth` policy with reply-constrained traces.
The interface fixes a public announcement schedule and its raw words separately
from the hidden environment. Neither the schedule nor that environment is an
argument to initialization: the actual initial heap and memory still come only
from the registered configuration.

The protocol acceptance relation must bind actual Start events to that schedule
and subsequent feedback to actual replies. At a fixed configuration and width,
`ofInput_history_independent` gives identical initial memories for different
schedules. The requirement covers every admitted width, with current-request
fitting and actual accepted executions as conclusions. Candidate-generated
queries, answer values, hidden inputs and implementation-chosen padding must
not be used as admission words. `ScheduledTraceTimeO.source` preserves acceptance
when projecting the same RAM trace to source.

This admits finite runs on sufficiently large fixed-word machines. It does not
implement dynamically growing words or supply future announcements to the
source. Use one `Session.Runs` for an entire persistent process, not a fresh
initialization for each job. The actual calls for new announcements, terminal
answers and all intervening feedback remain part of the same instruction count.

## Query and terminal replies

`Program.Output (Sum Query Answer)` fixes a reply layout for protocols that
either issue a query or return a final answer. It reuses `Representation.sum`:
the existing option/product layout contains exactly one payload. Both-present
and both-absent values represent no sum, and no absent array needs a default
allocation. `Output.sum_inl` and `Output.sum_inr` reduce correctness to the
selected payload's ordinary return-heap observation.

This output instance does not add native `Sum` syntax. Source programs can
construct the layout with the existing `some`, `none` and pair operations;
their normal compiler costs remain. A protocol must still specify its initial
request, subsequent feedback, and terminal condition. In particular, a terminal
answer can require an actual source call without consuming a query allowance.
Keep a suspended computation in the actual source state; a mathematical Lean
continuation is not an executable payload supplied for free.

## Operation and transport boundaries

For mutable buffers, `ArenaMeasured.read` and `ArenaMeasured.write` consume the
actual successful heap-operation equations and finite-word facts. The write
rule exposes the updated heap and the existing compiler's instruction count;
ordinary sequence composition then continues from that heap, without assuming
that aliases retain their old contents or that a store is free.

These bounds include each invocation's call/return wrapper and final halt.
They do **not** include initial arena bootstrap, host input preparation, result
serialization, or an external streaming driver. A complete interactive-task
bound must connect and charge those operations separately. This interface is
not itself an executable session runner or a theorem about one continuously
running I/O program.
-/
