# Frontend integration

This is the detailed acceptance checklist for the common declaration. Checked pieces do
not close the remaining integration obligations.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Active integration gate

The public target is one program declaration, not a choice between three
languages. `pure` and `effectful` describe semantic properties; a native function
is a mathematical proof view. They must not determine whether a program can
combine records, arrays, calls, finite loops and recursion. The existing typed
source and RAM backend remain shared; another wrapper around disconnected
frontends does not complete this gate.

The current integration work has these concrete obligations:

- [x] Parse one shared source declaration and register one set of function
  headers. Actual source identity, mathematical observations and optional model
  proofs are distinct fields; the separate native-function registry is removed.
- [ ] Share resolved types, operations and control-flow lowering, with existing
  entry modes retained only as compatibility or explicit proof-view choices.
  The default `source_program` now uses represented preparation and the shared
  source emitter; `(native)` retains its earlier naming convention through that
  same entry. The specialized `(pure)` preparer remains a compatibility path,
  not the recommended way to select language features.
- [x] Separate mandatory source/type preparation from optional mathematical
  models in the represented preparation pass. Expressions and calls propagate
  the absence of a model explicitly; actual function IDs and representation
  interfaces do not depend on generating a pure function. A promised
  correspondence proof failing is still an error, not silent model removal.
  General loops use source contracts instead of inventing a total pure model.
- [x] Lower general `while` with represented array/record locals through the
  existing source loop. Assignments update actual mutable locals across rounds;
  guards execute again at each actual heap. Raw buffer/node types keep their
  identity representation, not an inferred array/list contents observation.
  The existing array-record consumer uses a mathematical loop state and the
  shared named contract; its original represented correctness statement is
  retained. The default entry now accepts this same preparation path; its
  existing borrowed-buffer traversal, recursive splay and imported-buffer
  consumers retain their source contracts.
- [x] Reuse Core's actual call/primitive typing and operand normalization for
  raw buffer allocation, reads, writes and slices, and node construction/reads.
  All local source signatures are prepared before bodies, so a forward call
  needs no already-proved mathematical model. The existing allocating `make`
  now passes through represented preparation with its original Array contract;
  its fixed `Program` interface does not require a pure model.
- [x] Complete optional mathematical models for acyclic forward calls using
  resolved local-call dependencies. Mathematical candidates are completed and
  proved callee-first, independently of the written source function order,
  operation identities and import tables. A missing callee model removes its
  dependent mathematical candidates, not the source program. The existing
  record-append caller now precedes its helper; its original mathematical
  equation, `program_correct` and same-program RAM `TimeO` proof check unchanged.
  Mutual recursion still needs its own total contract, not an inferred
  termination claim.
- [x] Preserve actual statement branches, standalone calls, scratch scopes and lexical slots.
  Mathematical joins and hygienic local versions are proof-side only. The
  original linked-list `unconsBody` identity and compiled consumers still check;
  assignments and shadowing no longer require different source lowering.
  The original nested-scratch program retains its scope owners, early returns,
  cleanup contract and physical workspace bound. Reclaimed contents do not
  acquire an automatic total-function model.
- [x] Reuse shared nested binding patterns for represented calls and Option
  branches. Right-hand sides are evaluated once and only used projections are
  emitted. The original optional-buffer import chain retains its mathematical
  update/frame statements and compiler-derived body bounds. Its imported pure
  Option/product result uses the checked encoding and existing map identities.
- [ ] Finish local-return block integration and its construct coverage.
  Value-producing blocks have a real boundary for loops and scratch scopes. Core now has an internal boundary using
  an optional result local, gated continuations and the existing loop and scope
  semantics. Each scratch scope stages its own result and commits only after
  successful cleanup; fault exits really drop those temporary roots before
  checking the parent scope. The represented conditional/Option value-block
  preparer now uses this boundary instead of recursively replacing returns by
  assignments. Actual return-control checking is separate from optional models;
  assignments invalidate the affected enclosing mathematical locals.
  The existing record/List branch proofs check, and the List's exact RAM count
  includes the result assignment and final payload match. Existing ordinary
  traversal code and bounds are unchanged. Plain `let x : T ← do ...` blocks now reuse
  that same boundary and proof trace. The original structured scalar caller uses
  this form with its unchanged mathematical proof and RAM realization/invocation
  proof; shared Option normalization handles the private control values.
  The result's outer Option itself distinguishes a continuing block from a
  completed one, including `some none` when the returned value is optional.
  No separate activity flag or flag/result consistency proof is needed.
  Fully modeled `if`/`Option` choices, including nested mixed return/continue
  branches, retain the selected completion payload and current state before
  composing following statements. That continuation runs only when no local
  result was saved; actual source lowering retains the original branch and one
  shared suffix. Branch summaries carry only mutable lexical slots, including
  shadowed bindings; immutable observations still require the actual heap
  preservation proof. The allocating `chooseSum` value block retains its
  unchanged List-sum proof. A possible normal exit does not fabricate a completed
  result or admit a mixed body through the normal-fold gate; local-result ranges use
  the separate continue/return summary.
  The existing `Scope.work` now puts its nested scratch scopes inside a plain
  `do` value block. Visible completion contracts and actual execution frames
  hide private result slots from its source proof; cleanup still checks the
  full state and retains updates to older objects. Its mathematical contents
  and physical workspace guarantees concern the changed source program, not
  a claim that the added completion instructions are free. The existing
  `Scope.make` also has a reachable local return from a `while`
  inside its value block. Its visible loop contract and actual RAM workspace
  theorem check together. A normally continuing finite range inside a local
  `do` value block now retains its mathematical fold correspondence; the existing
  allocating List consumer uses this form with its unchanged replicate proof.
  Fully modeled `if`/`Option` bodies, including nested mixed-return branches,
  can also return from that local block: their control-sensitive summary gives
  a `forIn` model and checked heap-indexed correspondence. General nested loops
  and their mixed-exit combinations remain open.
- [ ] Generate mathematical-local loop interfaces from the resolved field
  representations. Normal represented rounds now retain their own mathematical
  traces independently of a whole-function model. The array-record consumer uses
  generated named mathematical locals, guard/body correspondence and `model_spec`;
  its proof supplies the invariant, decrease and exit result without raw environment
  transport or `Part` unfolding. The mathematical views select the same actual
  named source loop, adding no helper calls. Completion-aware rounds retain
  their local type/representation metadata independently of pure operation
  traces and reuse the same mathematical state generator. Their supplied
  guard/body contracts relate observations at the actual heaps; they do not
  require or generate a pure body transition. Extend automatic effect/frame
  composition across construct combinations. Fixed captured handles do not by
  themselves preserve captured contents, and no total model of the complete
  while is required. The normal-round interface currently requires checked
  array-preserving operations and no guard assignment to retained locals; it
  does not invent a transition for arbitrary aliased mutation.
  Its current `relationTrace` consumes pure-operation correspondence and global
  array preservation. Mutable calls need supplied effects for that actual source
  call, renewed observations for changed fields, and per-observation frames for
  retained fields; stale aliases cannot be carried forward unconditionally.
  Adding another relational WP expansion or choosing a raw handle from a model
  does not fill this gap.
  Local-return blocks also need an author-facing completion/local-state view:
  compiler-private result slots must not enlarge user invariants or scratch
  tuples. Keep complete source coordinates for execution and run scope cleanup
  before projection. The original Unit-valued scratch worker uses generated
  visible body/completion contracts and shared scope closure. Ancestor private
  slots are reconstructed from the same actual execution's frame; authors do
  not enumerate them. Local-return `while` now exposes visible guard/body and
  completion contracts: the shared well-founded rule requires invariant
  preservation and decrease only for continuing iterations. A local result exits
  through the actual masked guard, with no invented decrease after completion.
  `Scope.make` exercises this path. Its separate arena proof reuses these source
  contracts through shared completion-aware loop lifting; the named-loop tactic
  supplies checked private coordinates and frames. Its mathematical resource
  entry reuses the guard/body model contracts and their invariant, with no
  reconstruction of visible tuple relations or preservation proof. The source
  `Scope.loop_spec` now uses `model_completion_contract`: a source-named `mkModel`
  selects the mathematical locals, and shared consequence rules compose its
  mathematical guard/body contracts with its genuine invariant, descent and result
  arguments. There is no private `mono`/entry adapter or source tuple transport
  in this loop proof. This interface requires an explicitly proved
  model-and-heap-preserving guard and now specializes
  `model_completion_effects_contract`. The general rule passes the guard's actual
  final mathematical state and heap to the body through a supplied preparation
  relation, with descent relative to the pre-guard state. The corresponding
  arena-readiness rule reuses the same finite execution. These are checked
  contract composition, not automatic effect/frame inference; the current
  scoped consumer exercises the preserving specialization. Raw `Buffer`
  identity observes a handle, not its
  contents; the worker's actual update and reclamation contract is retained.
  General mathematical-local integration and broader locally exiting range
  combinations remain open.
  The scoped consumer's substantive guard/body proofs now use native triples
  over mathematical locals and the real worker contract. Its older visible-local
  theorems are short compatibility consequences. The generated proof action maps
  the original guard/body result, preserving actual control, completion payload
  and heap; it is not another executable implementation. This direct entry
  currently requires a proved complete identity-coordinate equivalence. General
  Array/List observations have no heap-independent inverse and still use the
  relational contract. Extending their direct proof workflow, effect/frame inference
  and remaining fragment-readiness ergonomics is still an integration obligation.
- [ ] Compose mathematical functions and state contracts through the same
  heap-indexed representation. A pure encoding is a special case; mutable
  array contents are not preserved by arbitrary heap extension.
- [x] Generate exact unchanged-heap equations and curried total contracts for
  supported default scalar and registered-record programs. Checked callee
  equations compose through conditionals and Option branches, with results
  encoded using the existing representation. The original scalar and record
  consumers now use the default declaration and retain their short mathematical
  and contract proofs. The checked raw-input reconstruction covers identity
  values and registered direct scalar/scalar-product records; it does not
  invent an inverse for Array/List observations or promise every composite
  parameter layout. Ranges and recursion retain their existing correspondence
  paths rather than receiving an unproved unchanged-heap equation.
  A result refinement or preservation of old array contents does not imply
  equality of the complete final heap.
- [x] Share well-founded while reasoning over a related mathematical state.
  Normal iterations supply the next model; guard/body heaps and early returns
  remain actual source outcomes. Existing local-value contracts are the
  equality specialization, exercised by the original mutable traversal.
  Named `rel_contract` additionally hides fixed captures through the actual
  guard/body frames; its mathematical model need not encode source pointers.
- [x] Permit array-valued records at branch joins without a fabricated default
  handle. The existing typed-program consumer selects a real record in one
  branch, then executes one common append call; its `Program.Correct` checks.
- [x] Integrate direct pure-source imports and represented self-recursion at
  actual intermediate heaps. The record consumer imports a scalar helper;
  the linked-list consumer allocates before recursively calling itself.
  Ordinary mathematical equations give their total source correctness.
- [x] Integrate normal finite ranges and mutable local bindings with represented
  state. The linked-list consumer allocates nodes on each round and has generated
  total source correspondence. The array-record consumer now exercises general
  `while` with an explicit mathematical-state contract after each real append.
  Fully modeled `if`/`Option` range bodies also support function-level return
  correspondence. Calls to the enclosing recursive function from a range and
  general nested-loop models remain open. The distinct local-result and
  function-return paths are described below.
- [x] Simplify the generated range's mathematical view to its mutable
  accumulator, closing over immutable captures. `List.foldl_hom` automatically
  connects it to the unchanged full source state. The existing List proofs use
  only their ordinary accumulators; the compiled linked-list consumer remains
  checked.
- [x] Publish `Program.TimeO` at input-dependent call depth. A supplied uniform
  polynomial depth envelope now gives code/stack capacity under the existing
  width policy; actual values, allocation and execution still require proofs.
- [x] Compose the actual generated entry and call-wrapper resource proofs from
  supplied operation certificates, using the existing structural rules rather
  than per-function ABI adapters or guessed operation prices. The original
  record append's full uniform `TimeO` proof now uses these shared passes.
  Result-dependent continuations still require their own source contracts;
  the passes do not infer mathematical invariants or data-dependent prices.
- [x] Select code independently of correctness: `program%` also selects an
  effectful raw entry when it matches the fixed input/output layout. Proofs
  are prepared by `program_correct`, not by selecting the candidate. The
  original allocating `make` consumer proves its ordinary `Array.replicate`
  result through `Correct.of_triple` and its existing standard state contract,
  without generating a total pure model first.
  `program_correct` also accepts an explicit represented total contract when
  the selected header has no model. The same packing bridge carries that
  contract to the fixed interface; no pure model or private ABI proof is needed.
  Matching raw layouts now select the original entry whether or not a model
  exists. Mathematical type/observation compatibility is checked when that
  model is used for correctness, not as a condition for selecting code.
  Direct represented models use their registered refinement; the existing
  bounded-increment `Program` now exercises this branch through the migrated
  default declaration and its unchanged ordinary minimum equation, alongside
  the contract-only and genuinely packed record consumers.
- [ ] Migrate existing consumers to the common entry and verify their ordinary
  correctness statements and same-program RAM bounds on 0v0. Update the manual
  and remove obsolete capability claims when those consumers actually pass.

Finite ranges now use the original in-place source lowering independently of
model availability. The emitter exposes the actual named loop, complete lexical
slots, entry bindings and body observations. The allocating List range's
mathematical fold is proved through that loop's actual `Control`/locals outcome;
there are no generated range-body or range-fold source calls. Its original
replicate equation and total correspondence check. The original traversal also
retains `Implementation.boundedMap_loop1` and its RAM cost proof, including the
same stable buffer-length bound without an extra temporary capture.

A normal finite range inside a local-result `do` block now uses the same actual
pending-controlled guard and increment. Its correspondence proves that the
active result slot stays empty, retaining every fixed source coordinate for the
continuation, including enclosing private slots. It specializes the shared
local-completion range rule and existing fold theorem; no second loop or
executable helper is generated.
The allocating List consumer keeps its original replicate equation and total
correctness proof. The added value-block control belongs to the actual compiled
program; this does not claim an unchanged instruction count. The normal-fold
path still requires both a normally continuing scope and a complete body model
and proof trace; a normal exit being possible alone does not justify a fold.

Fully modeled `if`/`Option` rounds with local return, including nested mixed
branches, capture `Option payload × state` at return and fallthrough leaves, using
the existing product and Option representations. The generated mathematical `forIn` and its
heap-indexed correspondence distinguish updated continuing locals from the
actual saved result. The active pending slot is not a fixed capture; ancestor
slots and other fixed lexical coordinates are preserved. The payload is typed
by the local value block, independently of the enclosing function's result.
The shared `observe_while_completion_rel_forIn_range_step` theorem connects this
summary to the same source loop and its actual endpoint heap. Only continuing
rounds advance; completion leaves through the real masked false guard using
`TotalWP.while_completion`. The shared continuation runs only on the absent-result
path. No second source loop, helper traversal or allocation is added for the
proof-side summary; real body allocation remains in the actual execution.
Branch summaries carry only mutable lexical slots, including shadowed bindings.
The prepared completion-range mathematical view likewise carries
`Option Result × Mutable`, with no cursor in its accumulator and immutable captures
closed over. `Stmt.forIn_range_step_completion_eq` applies `forIn_range_hom` twice
to connect this view to the full state: the embedding must reconstruct the full
body result on both continuing and completing rounds. Immutable observations
still require actual heap preservation; a fixed handle alone is not enough.
The reduced-state list proof and nested completion consumer have been checked
on 0v0, retaining their mathematical statements and generated correspondence.
The step still projects the full mathematical body result. Functions whose trace
contains a completion range receive `Family.f_model_eq`, exposing a locally
reduced body of `Family.f_model`, or `Family.f` in `(native)` mode. The equation
is used explicitly, not registered as a global simp rule. Its reductions are
limited to `Prod.map` through `Option.elim`/`if`, using `Option.elim_comp` and
`apply_ite`, plus `Id` pure/bind and concrete tuples. The checked List proof now
rewrites this equation before using its original mathematical induction,
without a per-field callback connection proof; nested `if`/`Option` consumers
are also checked. Arbitrary callbacks are not promised a simplest normal form.
The actual source/raw loop, heap and body trace are unchanged; this mathematical
simplification supplies no new RAM bound.

Fully modeled finite-range bodies with mixed `if`/`Option` branches also have
checked mathematical correspondence for direct function returns. They retain
the actual `Control.returned`/`whileReturn` path, without adding a local value
block or pending-result slot. A returned (`some`) round keeps its actual payload
and endpoint heap; it neither advances the cursor nor runs an additional false
guard. The control relation retains the actual raw payload, rather than choosing
one from the mathematical result. Raw lowering is unchanged, and this source
correspondence supplies no additional RAM cost bound.
General nested loops and their mixed-exit combinations, calls to the enclosing
recursive function from a range and full models of arbitrary heap mutation
remain outside this automatic mathematical-model path.

The proof preparer now follows actual branch continuations when composing
ranges, carrying their heap relations and frames. Combinations involving nested
loops still need consumer evidence; this does not close the complete
integration gate. Explicit imports retain their source tables, order and written
names, and resolved calls select those same entries. The frontend's buffer
operations use the internal emitter to avoid an import cycle. Existing exact
body identities and compiled consumers remain the compatibility requirements,
not names that can be restored with aliases.

This gate does not claim arbitrary Lean compilation, infer algorithmic invariants
or turn every mutable computation into a pure total function. It requires that
the already implemented capabilities work together without author-maintained
representation, environment or machine bridges.

The shared declaration must distinguish three pieces of information: its actual
source function and action; its mathematical types and heap-indexed observations;
and an optional proved total-function view. Absence of the last must not prevent
lowering a loop or an effectful call. In particular, two array parameters can
alias: their entry contents alone need not determine the result of a mutation
followed by a read through the other handle. Such a program needs a state
contract, not an invented contents-only pure function. Control-flow lowering
must be shared before the public entry modes are collapsed; trying several
frontends until one accepts the program is not this design.

## Current declaration and proof-view behavior

The intended interface is one program declaration. Arrays, records, calls,
mutation, loops and recursion are language features that must compose; authors
should not choose a frontend before combining them. Correctness can use an
ordinary Lean function equation or a mathematical state contract, depending on
the program. These are proof views of the same implementation, not different
languages or execution models.

**Current status: the default entry is connected; control-flow integration is
incomplete.** New programs should use `source_program P where`. `P.f` is the
actual source action, and `P.f_model` is its mathematical view when a checked
total model is available. The common entry has been exercised by the buffer,
recursive splay, imported optional-buffer and original traversal consumers,
including the traversal's RAM bound. The allocating List range now has its
ordinary mathematical proof through the original named loop. General
control-flow and nested-range mathematical-model coverage remain incomplete.
The [active integration gate](../ROADMAP.md#active-integration-gate) lists the
remaining work.

Ordinary local calls no longer need to be written after their helpers to obtain
a mathematical model. Source bodies and imports retain their written order;
only mathematical definitions and correspondence proofs are completed
callee-first. The existing record-append caller is written before its helper
and retains its original correctness and RAM time-bound proofs. An unavailable
callee model removes dependent mathematical views, not the underlying source
calls. This does not infer totality for mutually recursive families.

Existing `(native)` examples retain a compatibility naming layout for the same
preparation pass. `(pure)` remains the older scalar compatibility API with its
own preparer; it is not yet just a naming alias. These examples are evidence for
particular interfaces, not a recommendation to split an algorithm across three
source languages.

Integration now also connects represented records/arrays to scalar expressions,
direct pure-source imports and self-recursion, including actual allocation before
the recursive call. `Syntax.elaborateSourceProgramWithSites` supplies the
existing typed-source emitter; proof views must not re-enter public command
dispatch to select another frontend. Existing consumers exercise mutable local
bindings, allocating List ranges and array records. Their correspondence must
retain the same actual source calls and intermediate heaps through integration.
Conditional and Option value branches now use a real local-return boundary:
returning stores the result and stops that block's remaining control flow. The
optional result slot also records completion, so a separate activity flag and
its consistency proof are unnecessary. An optional returned value is stored as
`some value`, distinct from the initially empty slot even when `value = none`.
The existing record/List mathematical proofs check through this boundary, and the
List's exact RAM count includes its actual control instructions. The source
preparer no longer rejects loops or scratch scopes just because they occur in a
value branch. The local-return `while` in `Scope.make` has checked source and RAM
proofs; normal ranges inside local value blocks retain their fold models,
and fully modeled `if`/`Option` local exits, including nested mixed-return
branches, use the control-sensitive `forIn` model. General nested-loop
combinations remain open. Ordinary
`let x : T ← do ...` blocks use the same boundary. The existing structured scalar
caller uses this form and retains its mathematical and actual RAM proofs;
private Option control is simplified by the shared backend proof rules.
The existing nested-scratch worker also uses a plain value block. Its generated
completion contracts expose source-visible locals and distinguish fallthrough
from a local result. Actual execution frames reconstruct the compiler slots;
scope cleanup still checks those full locals before returning the visible view.
General represented `while` now retains actual assignments, effectful guards
and early function returns through the same source loop. The array-record
consumer supplies a mathematical-state contract, not a total pure function.
Mathematical range-view coverage for general nested loops and their mixed exits,
and calls to an enclosing recursive function remains
part of the integration gate. A normal range view folds mutable locals and
closes over fixed captures; a local-completion view also retains its payload.
The function-return view instead retains the real returned control and heap.
Each correspondence refers to the same named source loop, without adding source
helper calls or changing its charged execution.

Statement branches, lexical shadowing, standalone Unit calls, nested product
patterns and scratch scopes now pass through the same represented preparation.
Their actual source control remains distinct from proof-only result joins and
local versions. The original linked-list body identity, optional-buffer import
chain and nested-scratch consumers retain their correctness and compiled
resource statements as integration requirements. Scoped cleanup does not preserve
observations of reclaimed storage. The default entry uses the common preparer;
the allocating range and original traversal now retain their corresponding
mathematical and RAM proofs. Further combinations remain in the integration gate.

The [cross-prover research report](../DESIGN_RESEARCH.md) supplies the rationale
for a common mathematical contract layer with complementary function-equation
and state-invariant proofs. A model can describe mathematical Arrays or Lists
even when their implementation allocates. Conversely, arbitrary mutation of
aliased inputs need not have a total function of their entry-time contents;
its correctness remains a state contract. Generating a total model must not be
a prerequisite for accepting the underlying source program.

The independent scalar core now has
source correctness rules, generic whole-function lowering and proof transfer to
the existing executable RAM runner. Return-flag lowering avoids continuation
duplication and has exact static code-size formulas. A separate cost observation
of realized scalar executions now transfers source bounds to the actual runner,
including internal calls and the outer invocation overhead. The Lean-like
scalar `source_program` surface, independent `Part` observations, compositional
evaluation equations and a scoped strict Std.Do interpretation are now present.
Generated one-step function equations support ordinary mathematical correctness
proofs; shared structural rules compose separate cost bounds. Default declarations
expose semantic actions as `P.f` and optional checked mathematical functions as
`P.f_model`. Function equations and state contracts concern those same source
actions; the legacy `(pure)` API retains its original mathematical naming.
Generated contract equivalences hide argument-environment packing, and named
specification rules apply supplied contracts in native `mvcgen` proofs;
focused scalar tactics compose realization and uniform structural cost rules.
Source execution and function contracts carry typed locals and a shared heap;
their native monadic view retains the final heap on success and failure.
Borrowed-buffer length, reads, writes and slices now have source syntax and
semantics and checked whole-compiler behavior/cost connections. Mutable local
bindings and assignments use the same source state, native equations and lowering.
The typed core now includes effectful-guard loops and well-founded source rules.
The surface accepts `while` and generates named guard/body/loop equations,
normal-continuation proofs and termination rules over mutable locals and the heap.
The complete buffer traversal proof now gives its ordinary `Array.map` result,
preservation of disjoint views, termination, compiled invocation and independent
linear instruction bound.
A finite-range factorial also uses a generated native function: one accumulator
loop is proved equal to `Nat.factorial n` with ordinary fold/product identities.
Its total source contract follows from generated correspondence, not a second
termination or implementation proof. Factorial and the direct/composed/imported
compiled traversal modules exercise the finite-range and inferred-budget
interfaces. Their existing contracts and bounds remain integration requirements;
the updated entry must also pass the complete library, Examples and manual build.
A self-recursive factorial proof uses ordinary induction and mathlib's
`Nat.factorial`; its compiled invocation now has a separate linear instruction
bound, subject to word-range and code/stack-capacity conditions. The
[roadmap](../ROADMAP.md) records these boundaries and defines completion gates.
Typed program embeddings now preserve complete source observations, including
divergence and finite faults. Linking the existing traversal and recursive
factorial tables reuses their original native proofs without unfolding either
algorithm. The frontend now accepts `source_program P importing Library, Other where`
and qualified calls into those libraries. Added bodies use the combined table;
generated caller equations expose original library actions through proved
embeddings. An imported program can itself contain imports. Separate connection-layer
theorems now preserve realizability and exact compiled body counts through these
embeddings, including the actual callee frame and call overhead. Source action
equality alone is not the justification for those resource results.
Program sketches and proposed interfaces in the [design overview](../HIGH_LEVEL_LANGUAGE.md)
are schematic, not a claim that the complete language/API is available.
