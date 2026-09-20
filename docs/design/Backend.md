# Arithmetic realization and compiler connections

The independent language does not import RAM. This connection layer supplies
finite-word realization, lowering proofs and justified reuse of the register-IR library.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Nat is mathematical, Word is modular

Source `Nat` arithmetic keeps Lean's mathematical meaning. The initial RAM
realization is bounded-word arithmetic, not bignums. The compiler generates
source-level obligations for every executed intermediate that must be encoded.
For example, `(n + n) / 2` needs representability of `n + n`, not just of
the input and output.

Use the following primitive semantics and implementation policy. A row outside
the current milestone is rejected by that compiler subset until implemented,
not accepted as an uncharged host operation.

| Operation | Source meaning | Initial word-backend policy |
| --- | --- | --- |
| Nat literals, addition and comparison | Lean Nat and Bool operations | Scalar encoding and addition-range obligations; current scalar backend |
| Nat multiplication | Exact natural multiplication | Proved lowering with an actual intermediate-product range condition |
| Nat subtraction | Saturation at zero | Proved comparison mask applied to the wrapping word difference; no subtrahend-order premise |
| Nat division and modulo | Lean semantics, including `n / 0 = 0` and `n % 0 = n` | Existing word operations already match these zero cases; proved lowering requires representable operands, not a nonzero divisor |
| Explicit BitVec operations | Their specified modular/word semantics | Matching word operations and proved representation |

The first lowering is syntax-directed, not selected by a user's proof.
An invariant may discharge its range conditions; proof-guided removal of a
branch is a later verified optimization with its own cost connection. An
unresolved range condition does not authorize changing source semantics or
silently narrowing a published theorem's input domain.

Existing modular Word examples retain that meaning when migrated. No claim is
made that every unbounded-Nat program runs at arbitrary word width or that
arbitrary-precision arithmetic costs one RAM transition.

The current nested-expression consumer implements `n - (n / d) * d`. Its source
result follows from the ordinary Nat remainder identity, and the shared compiler
transfers that result to the actual callable implementation. Its range and cost
proofs remain separate; the bound counts division, multiplication and saturating
subtraction, not a different implementation using one remainder instruction.

## Three kinds of obligation

- Source correctness: array validity, mathematical invariant and termination,
  independent of the selected backend width, stack layout and proposed time
  bound. Explicit source `BitVec w` types still have their stated width semantics.
- Backend realizability: intermediate scalar ranges, physical storage for the
  represented objects, and sufficient maximum call nesting/storage.
- Backend mechanics: fresh slots, argument encoding, receiver updates, saved
  locals, code placement and instruction correspondence, solved by compiler
  proofs.

The second group is derived from source-level facts and exposed in those terms
when it cannot be solved automatically. A well-founded termination argument
does not automatically give a tight call-stack bound. Shared rules can derive
such bounds for supported recursion patterns without confusing them with time.

The current scalar realization API has shared `RealizationWP` rules, but its
consumer no longer applies them one source constructor at a time.
`ram_source_realize` opens ordinary arguments, reuses the supplied callee's
realizability and correctness facts and simplifies environment bookkeeping.
Without `using`, it stops at a call. `ram_source_call using resource, specification`
then consumes just that call's supplied realizability and source contracts,
retaining its actual returned value and final heap before stopping at the next
call. The caller can use a frame consequence to establish that next call's input.
The underlying intermediate-range and call-nesting facts remain genuine
source-level obligations. General callee selection and recursive automation
remain work for the richer language.

## Automatic proof transfer to the existing backend

A lowering artifact contains the actual `Stmt/Func` program and its concrete
representation/layout plan. Shared structural theorems relate source execution
to that artifact. Elaborator-generated certificates instantiate those theorems;
they do not search for a new simulation proof for each user program.

The artifact is fixed by the declaration and backend configuration. Its
certificate applies to all represented legal inputs, not a selected runtime
input, execution witness, time budget or correctness proof. A width-parameterized
artifact family is allowed under a fixed compilation/width policy; unrelated
per-input programs are not a uniform implementation. Later verified optimization
plans must respect the same boundary.

Required proof shape, with names only schematic:

```text
lowering_sound :
  Compiles source artifact ->
  Exec source input heap result heap' ->
  InputRep artifact input heap targetEntry ->
  RealizationConditions artifact thisSourceExecution ->
  exists targetFinish,
    TargetSafeExecution artifact targetEntry targetFinish
    and OutputRep artifact result heap' targetFinish
```

A semantic definition of realization conditions can quantify over the source
execution. Its public proof interface must instead generate arithmetic,
region-size and source-recursion conditions with a proved sufficiency theorem.
Do not ask users to assume target termination, an unexplained trace premise,
or precisely the register execution the compiler is supposed to establish.

Prove the source-to-IR cases once: values/operations, lexical scope, sequencing,
both branches, current-heap reads/writes, calls, loop iteration/exit and returns.
Maintain lexical environment and heap relations inside these proofs. The call
case composes the parameter/result relation and callee theorem, preserves source
caller locals and retains shared effects. Recursive soundness may induct over
finite source execution; source termination is proved independently.

Then compose with the existing `FunctionExec`/safe execution to RAM simulation
and runner theorems. Supported source programs require no per-function raw AST
adapter, layout record or proof that their whole body equals a library template.

A total source theorem plus a verified realization derives the compiled
termination theorem. The user does not supply an additional unexplained
`Halts` assumption. Code/stack/width obligations remain genuine and are
translated through the generated plan.

## Migration and module boundaries

Keep `Complexity/` as the only reusable library root. The
`Complexity/Language/` subtree holds typed syntax, independent semantics,
source proof rules and frontend support. Its semantics/proof modules must not
import RAM. Backend realization and lowering live under the existing RAM topic
and import both the language and current compiler. Final file splits follow
actual dependencies; do not create a hierarchy of empty placeholder modules.

Reuse rather than replace:

| Existing foundation | Role |
| --- | --- |
| Lean/Std/mathlib values, `Part`, monad transformers, `Std.Do` | Mathematical data and semantic proof infrastructure |
| `Ram.Source.Stmt/Func`, safe and measured execution | Backend IR and proved execution rules |
| Local compiler, typed/raw call and runner bridges | Actual code, safe execution and cost transfer |
| Array/indexed representation, slice and frame lemmas | Physical realization of abstract source objects |
| Recurrences, `IsBigO`, potentials | Mathematical analysis after source obligations are obtained |
| Named parser, source metadata and RAM tactics | Reusable frontend pieces, active backend proof tooling, certificate support and compatibility |

The existing `ram_def` interface remains supported while high-level declarations
are introduced separately. Do not silently change old word semantics, input
domains or measured programs. The independent high-level semantics is new work;
existing StateM postcondition wrappers do not count as its implementation.

### Lemma reuse through the connection layer

Old-DSL contracts, representation/frame lemmas and cost results should reduce
high-level proof work through `Compiler/Language`. This layer imports both sides
and proves reusable transport rules; the independent source semantics does not
import RAM or gain external-function forms merely to reuse a theorem. Ordinary
mathematics already in mathlib should be reused directly.

An algorithm author should apply a source-facing theorem whose proof reuses the
old library. The connection layer handles value representation, routine frame
transport and invocation correspondence once for a supported construction, not
through one hand-written register adapter per algorithm. Genuine range, aliasing
and storage conditions remain visible in source terms.

Transfer must respect its logical direction. The existing forward simulation
can map a realized source execution to the target and recover its result
property using an old contract and target determinism. It cannot derive source
termination from target termination alone. Such an API needs a separate proved
reverse/progress connection. Similarly, behavior equality alone cannot transport
an exact instruction count or justify replacing one implementation by another.

Selecting a verified old implementation for a high-level library call belongs
in this connection layer too. Its actual code, dependencies, behavior and cost
must be linked by proved correspondence. That capability is distinct from the
immediate goal of reusing lemmas; adding a foreign-call node by itself does not
reduce high-level correctness proofs.

A new lowering can produce different code. For migration, record whether it is
definitionally the old program or prove the new behavior and cost bounds.
Behavioral correspondence does not preserve old exact constants automatically.

## Backend and connection-layer work remains active

Maintain reusable register/state/frame, call/return, control-flow and measured
simulation rules alongside these milestones. They are first-class interfaces
for compiler maintainers, even when algorithm authors never see them. Extend
them for the actual new construction: total-frontend correspondence, richer
value encoding, heap growth or allocator-aware calls. Further return-flag
optimizations and linking variants are not the next high-level milestone.

Old-DSL theorem reuse belongs in `Compiler/Language`, not in source semantics.
The existing contract/time bridges for actual lowerings are useful; arbitrary
old implementation selection still needs proved implementation and cost
correspondence. Forward simulation alone does not derive source termination
from a target theorem. Source-to-source import transport is already implemented
and should be reused, not confused with completing this different bridge.
