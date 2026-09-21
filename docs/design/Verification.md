# Source correctness and proof interfaces

Correctness and successful termination are properties of the independent source
semantics. This document separates their author-facing interfaces from resource proofs.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Source semantics and ordinary Lean proofs

Define finite safe execution independently, with a schematic function-level form:

```text
Exec program function arguments heap result heap'

Total program function P Q :=
  forall arguments heap, P arguments heap ->
    exists result heap',
      Exec program function arguments heap result heap'
      and Q arguments heap result heap'
```

Source array bounds and valid views belong to safe source execution. Invalid
operations have a fault outcome, distinct from a returned value; a diverging
computation has no finite successful execution. Total correctness establishes
normal termination, not just absence of a counterexample. Neither source
execution nor source total correctness takes a proposed time budget.

The independent source observations make this distinction explicit.
[`Stmt.eval`](../../Complexity/Language/Eval/Basic.lean) has result
`Part (State Γ × Control result)`, preserving the final locals, shared heap and
finite control outcome. `Program.eval program fn args` is an action of type
`ExceptT Fault (StateT Heap Part) (Value result)`. Applying its initial heap gives
`Part (Except Fault (Value result) × Heap)`: fallthrough becomes `.missingReturn`,
including for Unit, while an actual return becomes `.ok value`. Both outcomes
retain the actual final heap; failure does not roll back earlier effects.
`Part.none` means there is no finite outcome; a finite fault is a defined error,
not divergence. Successful result equations are equivalent to finite returned
source execution and therefore include termination.

These noncomputable observations are determined by independent source execution
and determinism. They neither run the lowered RAM code nor choose a value from
the user's mathematical postcondition. The
[composition equations](../../Complexity/Language/Eval/Composition.lean) cover
skip, return, primitive binding, sequencing, conditionals and calls, preserving
return/fault propagation and lexical scope. They provide an equational
mathematical interface to the same source program, not a second algorithm.

The [continuation interface](../../Complexity/Language/Eval/Continuation.lean)
composes these observations through `Stmt.evalWith`. A normal outcome runs the
supplied continuation; a return or fault bypasses it. The call equation uses
the actual `Program.eval` action in the existing `ExceptT Fault (StateT Heap Part)` monad.
At a function boundary, falling through produces `.missingReturn`. The frontend
uses these proved rules to generate `P.f_eq`, rather than assuming a host `do`
block agrees with the typed source.

In the scalar example, `increment_eval` first rewrites `Implementation.increment_eq`.
Then `boundedIncrement_eval` rewrites its own one-step equation, reuses the helper
result and proves the two minimum cases using ordinary Nat facts.
`FunctionTotal.iff_eval` transports these successful result equations back to
the budget-free source contracts. `Env.forall_cons` and `Env.forall_nil` open
the typed arguments for that generic bridge. The mathematical argument is not
repeated in the contract or compiled-execution proof.

The function contract's precondition takes arguments and the initial heap;
its postcondition takes those same inputs, the returned value and final heap.
An observation equation fixes both the returned value and final heap. This
supports ordinary mathematical contents as ghost specifications when buffer
operations are added, without turning those ghosts into runtime snapshots.

Prove determinism of source outcomes and final state. Mathematical result and
cost observations must not depend on which proof of execution or termination
was supplied. Allocation uses the current object count as its deterministic
fresh identity, rather than an unspecified choice of fresh names.

Source predicates use ordinary Lean values, lists, arrays and relations.
A result specification need not be an independently implemented reference
function. For pure computations, determinism and termination yield ordinary
value equations; for mutation, they yield result/state relations and frames.

### Reuse Lean's termination arguments

For supported self-recursive mathematical models, supply ordinary
`termination_by` and, where needed, `decreasing_by` once. Lean checks the generated
native definition; generated correspondence reuses its recursion principle to establish terminating source
execution with the same result. The mathematical result theorem is then an
ordinary Lean proof, as in the factorial example. Both the default optional-model
path and the retained `(pure)` API reuse Lean's termination machinery within their
supported fragments. A source-only declaration does not acquire a termination
proof from an unchecked hint; the preparer reports that case explicitly.

Effectful total correctness reuses the same mathematical foundation through
source rules, without fuel or a time budget:

The represented preparation pass keeps actual source code and mathematical
types independently of its optional total-function model. It emits function IDs
and representation interfaces even without such a model, and does not register
nonexistent correspondence declarations. For a selected header without a model,
`program_correct ... using contract` accepts an explicit `RepresentedFunction.Total`
for that same entry and postcondition. Its packing transport reuses the real
source call. General represented `while` and statement conditionals now use
the existing source control flow. Its scope preparation drops obsolete contents
observations after unspecified effects, and mutable-value observations after a
loop. A raw `Buffer` or `NodeRef` retains only handle identity; it supplies no
validity, bounds or contents proof. Raw allocation, reads/writes, slices and
node operations reuse Core's own type checker and operand normalizer; forward
source signatures are available before their bodies or proofs. The original
allocation consumer now uses this preparation with its unchanged mathematical
Array contract. The default public entry now uses this pass. Complete range
correspondence and control-flow composition remain part of the integration gate.

- `TotalWP.while_wellFounded` accepts an ordinary `WellFounded` relation.
  `Stmt.observe_while_fixed_spec` exposes it through native `Std.Do` triples
  while fixing immutable captures internally. A named loop's `wellFounded_spec`
  takes a relation on `Loop.Mutable × Heap`; its invariant and normal/return
  postconditions still use named mutable arguments. Descent compares the end
  of a normally completed body with the state before the guard. A false guard
  or early return needs no descent. The existing `variant_spec` is the
  natural-valued `measure` specialization, not a separate termination checker.
- `TotalWP.while_rel` permits well-founded descent on a mathematical model
  related to the actual locals and heap. The corresponding
  `Stmt.observe_while_rel_contract` composes separate guard/body contracts;
  each normal body exit supplies a related next model. It needs no inverse
  from handles to arrays and does not assume captured array contents persist.
  The existing ordinary-local `observe_while_contract` now reuses this rule
  through the equality relation; the original traversal proof still checks.
  `Stmt.observe_while_fixed_rel_contract` retains fixed captures using their
  actual guard/body preservation proofs. Generated named loops expose it as
  `rel_contract`, with curried mutable arguments in the state relation and
  independent guard/body contracts. The existing fixed-local contracts are
  its equality-model specialization, not a second loop argument.
- `FunctionTotal.verify_wellFounded` supplies complete source-function contracts
  at smaller mathematical indices using `WellFounded.induction`. The index may
  select different functions and signatures for mutual recursion. This is a
  core proof rule; a convenient named effectful-recursion frontend remains open.

A terminating Lean definition returning `Part α` can return `Part.none`.
Termination of constructing that value does not prove its `Part.Dom`, still
less successful source return rather than a finite fault. `FunctionTotal` or
a strict native triple establishes the required successful execution. Separate
backend proofs retain word-range, stack and cost obligations; those are not a
second source termination argument.

### Public functions, effects and successful termination

The current action type is a general semantic representation, not the desired
mandatory type of every public function. Recursion does not imply a partial
interface, internal mutation does not require exposing the whole heap, and
backend memory faults need not become ordinary algorithm results. Keep general
execution available internally while distinguishing the public cases:

- A pure function, successfully terminating on its declared domain, should have
  ordinary Lean values and equations. Its result must be independent of hidden
  initial state, not merely leave that state unchanged.
- A borrowed mutable operation should have a mathematical contents/result
  contract that preserves actual sharing and frames. Read-only operations may
  still depend on the supplied contents; `NoHeapWrites` alone is not purity.
- A function using private mutable storage may have a functional interface only
  through a proved isolation and result-lifetime boundary. Freezing, ownership
  transfer and copying have different requirements and costs.
- An intended domain error may be an explicit tagged result. Invalid source
  memory access and backend capacity failure are different issues. The present
  compiler proves successful execution under its premises; it does not thereby
  implement every source fault as a checked runtime exception.

The shared user-facing foundation is a mathematical contract over the actual
implementation: typed inputs/results, contents relations, permitted effects,
frames and successful termination. Pure and mutable calls must compose through
these same rules. Mutable programs may use mathematical specifications and
invariants directly, without first constructing another pure algorithm.

The retained `(pure)` compatibility API generates a native total Lean definition
and its typed-core implementation from one supported buffer-free body. It reuses Lean's
recursion infrastructure and the author's one decreasing argument; generated
correspondence proves finite source execution with the native result, not just
equality conditional on successful execution. Scalar, Remainder and Factorial
exercise this path on 0v0, as does OptionalBuffer's nested structured metadata
helper. Self-recursion and acyclic calls are supported;
pure `while`, mutually recursive families and buffers remain unsupported.
Extending this fragment must retain the shared correspondence, not require
a second author-written implementation induction. A domain-restricted
total view needs explicit domain arguments or an implemented error result;
neither backend range premises nor an invented default value replaces this.

Finite-range integration must preserve its range origin, captured endpoints,
private cursor and actual body during elaboration. Existing finite-iteration
rules connect mathematical folds to source while execution; the remaining
generator work must apply them to the same named loop, not introduce a separately
called source implementation. General source control retains early returns.
Automatic mathematical views for broader nested-range and mixed-completion
combinations, and recursive calls inside ranges, remain separate coverage
obligations, not consequences of a finite index set.
Authors should not repeat library iteration or lowering proofs, and body calls
must reuse their checked correspondences at the actual intermediate heap.

This does not accept arbitrary Lean definitions as runtime primitives. The
frontend still controls the executable subset, supported operations and actual
lowering. Specifications remain free to use mathlib. Native Lean evaluation
has its host runtime; the certified complexity remains that of the
corresponding RAM artifact, not Lean's wall-clock execution.

A successful-termination certificate plus a result projection from the same
partial action can be useful shared proof infrastructure. It is not an adequate
replacement for the total frontend: a `Part.get` view is generally
noncomputable, and requiring the full desired correctness theorem before
publishing that view moves rather than removes the proof burden. Termination
may use algorithmic invariants, but no proposed time budget or reference answer
is allowed to define the implementation's result.

The generated native function and program identity have different roles.
Correctness may use ordinary function equality; cost and compilation theorems
remain indexed by the declared program/artifact. A cost function on extensional
Lean functions alone cannot distinguish two implementations with equal results.

The checked pure consumers are Factorial, Scalar and Remainder. Keep evaluating
the complete author proof, including termination and compilation transport,
when extending this fragment. In parallel, Traversal must lose its manual
`Control`/local-tuple/guard-body transport through shared loop contracts. The
pure path cannot be used to declare the mutable proof interface finished.
Conversely, a concise contents contract does not finish the executable pure
interface. For a supported private-state fragment, an ordinary total mathematical
state interpretation can be generated from the same body and related to its
mutable realization. Representation independence, permitted aliasing and result
lifetime remain necessary. A mutable return promises contents at return time;
a pure persistent result needs an immutable representation or proved,
appropriately charged copying/update discipline. Such a bridge is not
implemented, and does not automatically optimize arbitrary persistent updates
into destructive ones.

### Verification-condition generation

Generate source-level conditions from the typed program and prove, schematically:

```text
source_vc_sound :
  SourceVC program function P Q -> Total program function P Q
```

Conditions for bind/call/branch/loop are derived from the independent source
semantics. A call presents its real result and changed heap to the continuation.
Loop conditions expose the named live values and the user's mathematical
invariant/variant. Code navigation, variable bookkeeping and return propagation
are generated. The remaining goals are mathematical implications, callee
contracts and real operation preconditions.

Standard Lean tactics solve these goals. Failed automation leaves the source
condition and location visible. Missing compiler coverage is a language/backend
implementation task, not a request that the algorithm author prove `setReg`
equalities by hand.

### Reuse Std.Do without hiding a second implementation

The [generic Part adapter](../../Complexity/Control/Part.lean) reuses mathlib's
`Monad Part` and `LawfulMonad Part`. Its strict `Std.Do.WPMonad` interpretation
is enabled explicitly by `open scoped Part.TotalCorrectness`, not installed as
a global choice. It requires an actual returned value satisfying the
postcondition; `Part.none` has false weakest precondition. The existing monad's
`pure` and `bind` satisfy the required predicate-transformer laws.

The [source adequacy interface](../../Complexity/Language/Eval/Verification.lean)
connects source total correctness to the semantic result and native
`Std.Do.Triple`. Functions reuse `ExceptT Fault (StateT Heap Part)` with a false exceptional
postcondition: divergence fails the strict Part obligation, and finite faults
fail that exceptional postcondition. A generic strict Part WP alone need not
reject an error value; the source function specification supplies that policy.
The triple fixes the initial heap as a ghost and tests its equality in the
precondition, so a relational postcondition cannot confuse initial and final
contents. Existing transformer instances supply this composition.

The buffer actions now have native `@[spec]` rules. Reads and slices preserve
the actual heap; writes provide both their real write equation and updated
native contents, so alias/frame facts are not lost at the operation boundary.
`FunctionTotal.triple_spec` converts a supplied source contract into a native
continuation rule, including its actual final heap. Generated `P.f_spec contract`
specializes it to the named function's ordinary arguments. For example, the
buffer consumer uses `have clampSpec := Implementation.clamp_spec clamp_total`
and `mvcgen [clampSpec]`, without unfolding the helper. The supplied contract
retains its initial heap, actual returned value and final heap; no unchanged-heap
condition is imposed by the rule. The
[two-buffer composition](../../Examples/Language/TraversalComposition.lean) applies
the existing mutating traversal twice using these named contracts. The first
callee's frame preserves the second input, and the second frame preserves the
first result. Its proof uses `source_vc [leftSpec, rightSpec]`: standard `mspec`
steps continue the explicitly supplied contracts inside ordinary logical
obligations, and `buffer_frame` transports the supplied contents and frames
through actual intermediate heaps, including the outside-both conclusion. Neither
traversal body is unfolded. The rule does not guess
the callee's mathematical contract or register it globally. The scalar consumer proves
ordinary function equations by rewriting and Nat reasoning, and generated
contract conversion hides the typed argument packing. General mutable helper/loop
composition and elimination of routine ghost-witness packaging remain work
for the author-facing proof interface.
The backend's scalar tactics now compose realization and uniform cost rules;
they do not automatically discover mathematical contracts or recursive bounds.
These are semantic views of the core,
not acceptance of arbitrary host monadic terms as executable primitives.
The laws belong to the interpretation,
not unproved syntactic monad equalities for raw source trees.

A native list iterator visits fixed list values. For a mutable buffer, iterate
a captured index range and perform an actual read in each body; do not import
a snapshot traversal rule as the semantics of general mutable iteration.

An executable wrapper returns the result of the actual interpreter or compiled
runner. It does not choose an answer from a mathematical specification. A
proof-level `Part` observation is allowed, but is not the executable backend.

## Function-proof milestone

**Status:** `source_program (pure)` generates native total functions over scalars
and their products/options, checked action correspondence and total source contracts.
Scalar, Remainder, self-recursive Factorial and OptionalBuffer's nested metadata
helper pass on 0v0. Finite-range `for` also generates a native iteration and its
source correspondence from one body. `Iterative.factorial` proves the ordinary
`Nat.factorial` equation using fold/product identities, then reuses generated
totality without another loop termination proof. In this pure frontend, the
supported call graph is self-recursion plus acyclic calls; general `while`,
mutual recursion and buffers remain unsupported. Effectful declarations already
resolve forward and mutually recursive calls through their shared signature table.
The iterative consumer covers one range with an accumulator; it does not yet
establish consumer coverage for nested ranges, early returns or recursive calls
inside a pure range.

The default represented frontend separately supports fully modeled `if`/`Option`
finite-range bodies with mixed continuation and direct function returns. Their
generated mathematical model and heap-indexed correspondence retain the actual
returned payload and final heap; the single-range List equation has been checked
without changing its statement. This path adds no local value block or pending
slot and leaves raw lowering unchanged. Automatic action correspondence and
refinement are also checked for two nested finite ranges with an inner function
return. These connect the generated model to source execution; algorithmic
identities remain separate mathematical obligations. A private allocating List consumer
also proves the batch result `(budget, (values.take (batches * budget)).reverse)`.
Broader nested-loop combinations, general mixed local/function completion, recursive calls from a
range and full models of arbitrary heap mutation remain open; source
correspondence does not itself prove a RAM complexity bound.

Supported typed `do`, `if` and Option/List `match` value bindings share generated
state-carrying models and action correspondence for outer mutable bindings used
by the continuation. The mathematical observer carries the terminal
payload and final mutable state, using a heap-indexed relation rather than a
generated unchanged-heap exact equation. The algorithm's final result equation
remains a separate mathematical proof. A private state-carrying List consumer
proves the exact result `(decide (values.length < budget),
(values.take budget).reverse, values.drop budget)`; a scalar/Unit local-return
case without a range also retains its mathematical equation. Direct typed
`if`/Option/List `match` consumers also have checked exact equations for scalar
updates and allocating List transfers through nested value blocks. Sharing this
proof boundary does not infer frames for arbitrary effects or close the remaining
loop, recursion and RAM-resource obligations.

All source declarations expose ordinary-parameter `f_contract`, `f_args` and
`f_onArgs` interfaces. They reuse the existing source contract and argument
environment, not another semantics or a cost inferred from an extensional
function. Public splay and traversal contracts no longer repeat environment
projections. Splay uses a standard `Std.Do` triple with shared `Input`/`Post`;
ordinary inorder/search properties and their BST/frame consequences remain
inspectable in its specification module.

These declarations establish the first pure source-proof gate. Preserve their
single-body, single-termination-argument construction while improving the interface:

1. Retain the generated public function, its equations and checked
   connection to the existing core. Keep implementation identity for costs
   even when behavior is exposed as an ordinary Lean function.
2. Reuse Lean structural/well-founded recursion and the existing source
   [recursive contract rule](../../Complexity/Language/Verification/Recursion.lean).
   Generate ordinary-parameter recursive hypotheses and discharge scope/call
   transport. The author supplies genuine descent, not a time bound or RAM depth.
3. Share successful-termination and result-contract infrastructure. Do not define
   the public function by extracting the answer from its desired specification.
   Pure semantic projections require proved result independence from the heap;
   executable native definitions require the stronger generated correspondence.
4. Normalize generated equations so arithmetic definitional equalities and
   monadic administration do not require a restatement of the whole goal.
   Keep recursive bodies opaque until deliberately opened.

**First source-proof gate — checked:** the author proves
`Implementation.factorial n = Nat.factorial n` by ordinary induction and gives
one native `termination_by`/`decreasing_by` argument. Generated correspondence
and total-contract conversion remove manual `ExceptT/Part/Heap/Env` conversion
and a second implementation induction. The generic RAM chain and separate
resource conditions remain; all Examples and both aggregate library/Examples
builds pass. Native Lean execution and RAM instruction cost are distinct runtimes.

**Reconsider when:** the new API only shortens the final theorem while requiring
the old proof first, or the correspondence is a new hand-written adapter for
each function. A small alias or an additional `simp` lemma does not meet this gate.

## Mutable-contract milestone

**Status:** shared objects, aliases, operation specifications and the original
complete traversal proofs are checked. Named `wellFounded_spec` and its Nat
`variant_spec` specialization separate source termination from resources.
The frontend supplies independent `guard_contract`, `body_contract` and
loop `contract`, composed by `wellFounded_contract` or `variant_contract`.
They expose mathematical mutable variables and actual endpoint heaps, keep
immutable captures fixed, and retain separate normal/early-return postconditions.
Traversal uses them through the actual halted RAM result, including its two-call
and imported clients. Generated `spec` rules handle native continuations;
`while_contract_fixed` and `while_contract_fixed_of_total` reuse the same source
facts inside cost and realization proofs. Their shared implementation extracts
actual postconditions and preserves fixed captures. No nested round contract,
per-example execution adapter or repeated termination proof is required.

The named `count_frame_contract` also composes the traversal and copy loops'
existing guard/body contracts. It proves the remaining-count decrease and
accumulates their supplied transitive heap frame; the consumer retains its
array invariant, update proof and exit consequence. The frame starts at the
caller's supplied heap, not necessarily the current loop entry. This rule
requires a count-and-heap-preserving guard and count increments by one, with no
successful early return. It does not infer a mutable operation's effects,
strengthen slice disjointness to distinct objects, or supply a resource bound.

The [named-loop resource tactics](../../Complexity/Computability/Ram/Compiler/Language/LoopTactic.lean)
now remove view/frame selection and contract-to-totality setup from the compiled
traversal. They read the actual registered `Code` and supplied block contracts;
their proof terms reuse the existing loop rules. The cost form consumes uniform
guard/body certificates and an explicit remaining-iteration function. The
realization form retains a separate source precondition, including any extra
frame facts, and leaves nontrivial postcondition consequences to the author.
Entry into the body, preservation, numerical inequalities and actual word ranges
remain mathematical work. Mutable-coordinate patterns still occur in those
leaves. General potentials and allocating loops retain their existing public
rules rather than being silently reduced to this specialization.

The checked [source-frame rule](../../Complexity/Language/Effects/Heap.lean) uses `NoCellWrites` for the
statement and every callee preserves an exact heap-object prefix and existing
contents through actual execution, including faults. It permits allocation
initialization but conservatively rejects explicit cell writes; the allocation
consumer's `retained_frame` now uses this rule.

The shared [`buffer_frame`](../../Complexity/Language/Heap/Tactic.lean) finishing
tactic composes already supplied `Buffer.PreservesOutside` and `Contents`
observations through their actual endpoint heaps. It reuses Aesop's logical
rules and the symmetry of known `Buffer.Disjoint` facts, without global Aesop
rule registration, array simplification or new alias assumptions. The two-call
correctness proof uses both supplied callee contracts through
[`source_vc`](../../Complexity/Language/Verification/Tactic.lean): standard `mspec`
steps continue their actual WP. Beyond standard logical conversions, only
generated argument projections are simplified before the shared frame finish.
The allocating `Buffer.Copy.append` proof also reuses it for the second input
and final frame. Its fresh allocation, copied-array
identity and capacity inequalities remain explicit mathematical work.
Direct and imported traversal resource proofs reuse the same frame finish for
their second call, without unpacking the first callee's postcondition by hand.
Their actual launch conditions and independent instruction bounds are unchanged.

Borrowed-buffer APIs remain useful for explicitly in-place algorithms. Their
specifications should expose ordinary contents, lengths, results and permitted
updates. Library rules retain the actual heap internally; clients must not
confuse an old contents observation with the state after a mutating call.

1. Preserve the checked source/resource contract reuse, inferred structural
   budgets, coordinate normalization and named-loop setup. Extend these shared
   interfaces where general potential or allocating consumers still repeat
   connection work. Lexical tuples,
   guard/body sequencing and impossible control exits belong in shared rules,
   not repeated algorithm proofs. Keep general effectful guards and genuine
   early-return behavior intact.
2. Retain the checked composition of supplied callee frames with `buffer_frame`.
   Extend it only where real consumers need further consequences of
   `Buffer.Contents`, `Disjoint`, `PreservesOutside` and native `Std.Do` rules.
   Contract content, footprint inclusion, real overlap conditions and
   algorithmic invariants remain author choices.
3. Share invariant and shape consequences with realizability and cost proofs.
   A different resource proof should not repeat the array-correctness argument
   merely to recover a length or unchanged region.
   Abstract callees may export a callable upper-bound function with an `IsBigO`
   theorem. Its useful monotonicity is a property of the selected bound, not an
   assumption that exact runtime must be monotone.
4. Retain the checked captured-index traversal rather than add another iterator
   model. Effectful `for i in [start:stop]` freezes its bounds
   and uses an immutable index; `for x in xs` borrows a fixed view and reads its
   current cell each round. Both lower to the existing while semantics, with
   actual guard/read/update costs. A snapshot is not mutable-loop semantics.

**Advance when:** the current Traversal and two-call/imported clients are proved
using a prefix invariant, Array mathematics, descent and actual frame facts,
without manual `Control`/local-tuple/WP-transformer transport. Two disjoint
slices of one object continue to work. Other overlapping views retain their
existing semantics. More concise proofs obtained by assuming no heap effects,
global no-aliasing or a special initial heap do not qualify.
