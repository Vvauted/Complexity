# Roadmap

Write one high-level program, state its correctness with ordinary Lean/mathlib
values, and prove its complexity with ordinary mathematics. Shared compiler
proofs connect both claims to the same implementation. RAM is the backend, not
the algorithm author's proof language.

The [language design](HIGH_LEVEL_LANGUAGE.md) states the semantic boundaries;
the [module guide](STRUCTURE.md) explains the implementation's dependency layers.
Detailed mechanisms and acceptance obligations live in the linked topic documents
below. These milestones are capabilities, not a serial queue: memory, proof
interfaces and backend support must develop together.

## Active integration gate

**Still open.** New programs should use `source_program P where`.
Its actual source action, heap-indexed mathematical observations and optional
total-function model are distinct. A missing pure model must not reject an
otherwise supported effectful program.

The [complete integration checklist](design/Integration.md) records both checked
work and every remaining obligation. The outstanding work is:

- Share resolved operations and control-flow lowering completely; retain
  `(native)` naming compatibility and the older `(pure)` preparer without
  presenting them as separate recommended languages.
- Complete function-level range returns, general nested loops and their
  mixed-exit combinations, and calls to the enclosing recursive function from
  ranges, using the same actual named source loops.
- Generate mathematical-local guard/body interfaces from field representations;
  authors supply invariants, descent and genuine effect/range facts, not private
  slots, raw-environment transport or `Part` plumbing. Normal array-preserving
  rounds now have generated named mathematical locals and correspondence, used
  by the array-record while consumer. Completion-aware rounds reuse the same
  field representations through supplied effect contracts. The scoped loop's
  guard/body source proofs now use native mathematical-local observations;
  loop correctness and arena composition reuse those same contracts without
  manual visible-tuple or entry transport. Direct native proof entries currently
  require complete identity-represented locals; general heap-backed observations
  retain their relational contracts. Mathematical loop composition now also
  accepts effectful guards: their actual final model and heap feed the body,
  while continuing rounds decrease relative to the pre-guard state. The
  preserving-guard interface is a specialization of this general rule.
  Next extend the direct proof workflow to non-identity field representations,
  automate supplied effect/frame contracts across construct combinations,
  and simplify remaining fragment
  readiness proofs without hiding an equally long private adapter.
  Do not assign a pure transition to arbitrary mutation or mistake a retained
  buffer handle for unchanged contents.
  For non-identity fields, retain actual local witnesses and their heap-indexed
  relations: a mathematical array does not determine its handle or aliases.
  The missing automation is transporting these observations through actual
  effects and completion, using operation frames. Merely expanding `BlockSpec`
  into another relational WP does not supply that automation.
- Compose function equations and state contracts through the same heap-indexed
  representation, including actual aliases and intermediate heaps.
- Migrate the remaining existing consumers, retaining their original mathematical
  statements and same-program RAM bounds, and check the library, Examples and
  manual together on 0v0.

**Checked local-return boundary:** nested scratch and `while` value blocks now
use visible completion contracts. `Scope.make` exercises a reachable local
return from its loop; the source contract and actual RAM workspace theorem have
been checked together. The shared rule requires invariant preservation and
decrease only for continuing rounds. Cleanup still sees the full state, and all
added control instructions belong to the changed compiled program. This does
not finish general mathematical-local automation or range integration.
Normal finite ranges with fully modeled bodies inside local `do` value blocks
retain their fold model, including allocating iterations. Fully modeled
`if`/`Option` rounds, including nested mixed return/continue branches, instead
have an `Option payload × state` summary and Lean `forIn` model for local completion.
Correspondence retains the actual result, locals and heap of the same source
loop: only continuing rounds advance, and a completed round leaves through the
real stopped guard. The active pending slot may change; ancestor slots and fixed
captures remain preserved. The local payload need not have the enclosing
function's result type. This adds neither a second source loop nor runtime
allocation for the mathematical summary. General nested loops and their mixed
exits, function-level range returns, enclosing recursion from a range and full
models of arbitrary heap mutation remain open; no new RAM bound follows from the model.
The scoped while's resource proof reuses the visible guard/body contracts through
a shared completion-aware readiness rule, without a second termination proof or
manual `Part`/private-slot reconstruction. The same ranges, scratch capacity and
physical workspace bound remain explicit. A named-loop entry selects the checked
completion coordinates and frames. Its mathematical entry now reuses the same
guard/body model contracts, rather than restating their state/effect relations;
word ranges, fragment readiness and capacity remain explicit.
Named fragment entries normalize guard/body coordinates and compose an actual
standalone call with its scalar continuation. The scoped consumer no longer
assembles argument environments or splits call/sequence executions by hand;
it supplies the worker's existing certificate and ordinary range facts.
General allocating continuations still use the underlying readiness rule.
The source proof uses `model_completion_contract` to compose its mathematical
guard/body contracts with the invariant, progress and result facts. Their native
proof entries map the original actions through a proved identity-coordinate
equivalence, retaining actual control, completion payloads and heaps. Older
visible-local contracts are compatibility consequences, not separate proofs.
Local-state representations survive without a pure body model; the raw buffer
field observes only the handle, with contents still proved by the worker contract.
The final stopped guard also has a shared realization rule, retaining the saved
result's range condition rather than a private payload-slot proof.
Nested scratch proofs consume their existing visible body contracts directly;
the remaining callbacks establish non-escape and the postcondition after
trimming the actual final heap. This retains intervening writes, not an entry
heap snapshot. General effectful-guard contract composition is proved at source
and RAM-readiness levels; the current scoped consumer exercises its preserving
specialization, not automatic inference of a mutating guard's contract.

## M0 — Decisions and questions to settle

Retain one user-written implementation, independent typed semantics, budget-free
correctness and termination, actual sharing/effects, and backend-derived costs.
Reuse Lean, Std and mathlib without changing dependency pins or adding CSLib.
The [abstraction boundary](HIGH_LEVEL_LANGUAGE.md#the-abstraction-boundary)
assigns mathematical obligations to authors and routine lowering to the library.

## M1 — Function definitions and proofs that feel like Lean

Generated ordinary functions and checked total-source correspondence work for
supported scalar/structured and represented fragments. One native termination
argument feeds correspondence; `Part.get` of the desired answer is not the
implementation. Fully modeled mixed return/continue `if`/`Option` branches,
including nested branches, compose inside local value blocks and their finite
ranges. A completion summary retains the selected payload and state; following
statements run only on continuation. General nested-loop combinations remain open.
Mutual-recursion proof ergonomics, broader combinations and
equation normalization remain work. See the
[function-proof milestone](design/Verification.md#function-proof-milestone).

## M2 — Mutable algorithms with mathematical data contracts

Traversal, disjoint slices and imported/multiple calls reuse mathematical contents
and actual frames. Traversal and copy compose their counted loops through one
shared rule for descent and transitive frames, retaining their existing array
invariants and update/exit proofs. Shared loop rules and tactics remove part of
the lexical and execution transport. General mathematical-local interfaces, potential/allocation
setup and routine witness packaging remain open. See the
[mutable-contract milestone](design/Verification.md#mutable-contract-milestone).

## M3 — A language that can express structured algorithms

Supported records, products/options, shared Lists, arrays, calls, loops and
self-recursion must compose through the common entry. The
[data/operation coverage](design/Containers.md#language-and-data-coverage),
[frontend](design/Frontend.md) and [container composition](design/ContainerFrontend.md)
documents retain the exact scope. General element layouts, dependent/refined
runtime types, general patterns, closures, remaining numeric operations,
`break/continue`, I/O and persistent array encapsulation are not complete.
A mathematical container view alone does not implement its runtime operations.

## M4 — Allocation, lifetime and encapsulated local mutation

Monotone initialized allocation and scoped scratch reclamation have checked
source semantics, compiler connections and consumers. Rootedness, backward links,
aliasing and finite capacity remain explicit. General lifetimes and persistent
pure results are open; physical workspace is not exact peak-live space.
See the [memory milestone](design/Memory.md#allocation-and-lifetime-milestone)
and [scoped reclamation checklist](RECLAMATION_TODO.md).

## M5 — Source-level complexity and complete published claims

Same-execution instruction bounds, structural budget composition and fixed-type
`Program.Correct`/`Program.TimeO` interfaces are checked, including uniform
linear time for native record append. Further operation adapters, general
loop/recursive resource composition and source-facing space observations remain
open. See [resource analysis](design/Resources.md) and
[container resource composition](design/ContainerResources.md).

## Evidence and backend maintenance

The [consumer evidence](design/Consumers.md) distinguishes source correctness,
complete RAM results and remaining limitations. Its splay section records the
checked access/sequence proof and retained initial potential; top-tree mathematics
does not supply a dynamic logarithmic implementation.

[Backend and connection-layer work](design/Backend.md) remains first-class:
compiler maintainers need reusable register, frame, call/return and measured
simulation interfaces even when algorithm authors do not see them.
Behavioral equivalence alone transfers neither termination backward nor exact
instruction counts.

## Next work and when to change direction

Scoped reclamation and its same-source physical workspace guarantee are checked;
see [RECLAMATION_TODO.md](RECLAMATION_TODO.md). General lifetime inference and
encapsulation are not consequences of those theorems. The first bottom-up allocation queue is complete; see
[FOUNDATIONS_TODO.md](FOUNDATIONS_TODO.md) for its scope and checked builds.
The checked foundations include allocation, linking, source/resource contracts,
array-task statements, top-tree mathematics, native finite ranges and inferred
uniform budgets. Their successful consumers establish the stated supported
fragments, not missing container, lifetime or dynamic-algorithm interfaces.

The complete splay path already uses shared mathematical input/output contracts,
named cost selection and a typed runner result. Its tree descent, representation
and logarithmic potential arguments remain genuine mathematical work. The next
improvement should make another author reuse these interfaces without learning
environment encodings or repeating source facts in a second resource proof.

1. Extend the checked allocating-call proof pass from its current ordinary
   constructor, fold and typed-join consumers. Uniform wrapper budgets follow
   from `StmtArenaCostBound` and supplied callee certificates; the two straight-line
   constructor wrappers retain their exact counts. `ArenaMeasured.execute_le`
   shares publication with independent mathematical specifications; `execute_eq`
   retains exact body and invocation counts in the constructor-pair and selected-branch
   consumers. Known returned values no longer need existential witness packaging
   in the structural pass. Indexed calls
   now compose supplied mathematical-input bounds, and the shared ghost-indexed
   arena loop rule is used by the actual-only fold cost proof. `push` and
   `reverseAppend` use inferred wrapper costs, preserving their published bounds.
   Source postconditions now also flow into later input-dependent call budgets;
   the allocating `reverseSum` path uses this to traverse its actual new List.
   Direct measured-call composition now removes execution-witness unpacking in
   the reverse/append and allocation-then-traversal resource proofs. Continue
   composing supplied loop contracts: the fold now lifts its existing finite
   source loop through the shared indexed readiness rule, with time bounds
   applied separately to that same execution. Remove remaining resource-result
   bookkeeping without assuming arbitrary potentials, budget comparisons or
   guard/body admissibility can be inferred. The fixed-heap
   `StmtCostBound` cannot silently stand in for a bound on allocating execution;
   retain the existing arena cost relation and function contracts. The `prependPair`
   and `reverseAppend` migrations include their leaf wrappers: removing argument environments from
   the outer theorem alone is not enough. The allocating fold now reuses its
   ordinary-parameter measured entry without constructing a resource index.
   Extend that operation interface where actual consumers still assemble one,
   and compose the structural pass with existing loop/recursion contracts. Arbitrary resource
   indices cannot be guessed from raw handles; frontend metadata may expose the
   correspondence, not assert operation prices. Reuse the loop-specific coordinate
   pass and named-loop setup while removing remaining resource-result packaging
   in existing consumers, retaining the supplied leaf contracts, ranges, capacity
   and mathematical bounds. The traversal now selects its view/frames and reuses
   `TotalWP.of_blockSpec` through shared tactics, with no private adapter.
   Its proof leaves still contain mathematical mutable-coordinate patterns;
   general potential and allocating-loop setup are separate follow-up work.
   The two length-indexed List fold cost certificates now use
   `FunctionArenaCostBound.mono` to strengthen their mathematical preconditions
   and compare budgets, without unpacking executions. The shared rule reuses
   the same execution, readiness and compiler cost; it does not infer a budget,
   word range or capacity.
   Reuse source totality and actual heaps without another per-program termination
   proof. A shorter public theorem must not hide an equally long private
   connection proof.
2. Preserve native finite-range correspondence and inferred uniform budgets.
   The prepared local-completion `forIn` view carries `Option Result × Mutable`,
   erasing the cursor from its state and closing over immutable captures.
   `Stmt.forIn_range_step_completion_eq` reuses `forIn_range_hom` twice,
   requiring reconstruction of the full state after every round, including early
   completion. The reduced-state list proof and nested completion consumer have
   been checked on 0v0; source execution and its heap/body trace are unchanged.
   Functions whose trace contains a completion range now receive `Family.f_model_eq`
   for explicit rewriting of their mathematical body. Local reductions move
   `Prod.map` through `Option.elim`/`if` using `Option.elim_comp` and `apply_ite`,
   and reduce `Id` pure/bind and concrete tuples; no global simp rules are added.
   The checked List proof uses this equation and its original mathematical
   induction without per-field callback transport; nested branches are also
   checked. This does not promise a simplest normal form for arbitrary callbacks.
   Next connect function-level finite-range returns to generated mathematical
   models through the existing return-aware range observation rule. Preserve the
   actual `.returned`/`whileReturn` payload and heap without introducing a local
   value block or changing executable control and cost.
   Dependent bounds, recursion descent and algorithmic potentials remain
   mathematical obligations, not guessed annotations; no new RAM bound follows.
3. Extend the represented native frontend from its checked scalar, List and
   recursive product/option result joins. These compose their heap-indexed
   relations across allocation, with real slot initialization and field copies.
   Scalar `headOr` and compound `inspectOrPrepend` have same-invocation RAM
   resource theorems; `headOption` still has only source correctness. Extend
   remaining operation and pattern interfaces through these shared cost and
   publication rules, retaining actual callee readiness and capacity. Preserve the
   selected branch's heap, old shared tails and separate compiler-derived cost; do not
   evaluate or charge both branches. List matching already invokes the actual
   Uncons root/read operation before the existing Option match. Preserve that
   path, not a heap-independent inverse or free mathematical decomposition.
   Compose preservation only for proved-stable leaves and their combinations;
   mutable arrays and exact-heap observations are not stable under arbitrary
   shape extension. Extend List operations and their ordinary-parameter resource
   interfaces on this basis, retaining one declaration and its mathematical
   function. Further operations and lifetime machinery should follow concrete
   missing capabilities, not an algorithm catalog. This fragment is not a
   complete persistent collection library.
4. Develop source-facing space observations and composition over the actual
   execution, separating sufficient capacity, reserved storage and peak live
   data. Keep input loading, query drivers, width policy and word-versus-bit cost
   boundaries explicit; neither a bigger capacity assumption nor a theorem about
   isolated preloaded calls supplies these missing claims.

Before broadening an interface, review the complete author proof: what
mathematical work remains, what bookkeeping disappeared, and what assumptions
changed? If a short public theorem depends on an equally long private adapter,
revise the interface. If a memory choice prevents a required sharing or returned
value pattern, revisit that choice before expanding its API. If a generic rule
has no consumer beyond its own demonstration, do not expand a theorem catalog.

The [research report](DESIGN_RESEARCH.md) records the cross-prover evidence and
decision boundaries; the [literature notes](LITERATURE.md) connect individual
results to existing mechanisms. Neither transfers another system's cost model
or guarantees to this repository. Further research should answer a concrete
open obligation, not delay the shared interface work indefinitely.

Use existing Lean consumers for implementation checks on 0v0; no local
compilation, checksum machinery or unrelated test framework. Design-only changes
need no Lean build. Keep current capabilities and planned interfaces visibly
separate, and update this roadmap when the evidence changes rather than append
another implementation diary.
