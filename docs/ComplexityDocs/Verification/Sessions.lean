/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Session
import Complexity.Computability.Ram.Compiler.Language.Session
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
