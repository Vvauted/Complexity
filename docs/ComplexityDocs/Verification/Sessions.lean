/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session
import Complexity.Language.Session.Refinement
import Complexity.Computability.Ram.Compiler.Language.Session
import Complexity.Computability.Ram.Compiler.Language.Session.Induction
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound
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
