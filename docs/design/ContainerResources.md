# Container resource composition

These contracts count actual calls and retain their returned values, heaps and
allocation cursors. Source correctness is independent of the chosen resource bound.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Checked clients and reusable rules

The [native allocating consumer](../../Examples/Language/LinkedListAllocation.lean)
connects both `NativeConstruction.prepend` and `prependPair` themselves to the
halted RAM runner.
The shared [constructor-call bridge](../../Complexity/Computability/Ram/Compiler/Language/List/Cons/Call.lean)
reuses the imported constructor's measured execution and the existing call/return
rules. The wrapper's exact instruction count includes both call levels,
initialization, its own return and final halt. The same result retains the fresh
root, actual final heap, shared old tail and cursor advance of three words,
independent of tail length. Input loading remains outside the bound; word,
code/stack and arena capacity remain explicit. The two-call consumer invokes the
actual `prepend` body twice, retains the first call's heap and cursor, and proves
an exact six-word cursor increase and complete invocation count. Sequential
calls reuse the caller depth rather than summing their nesting allowances.
The shared [allocating-call composition](../../Complexity/Computability/Ram/Compiler/Language/Arena/FunctionResources/Call.lean)
accepts either exact measured callees or independent correctness, resource and
cost contracts. It retains actual returned values, heaps and cursors for the
continuation, using the existing execution and compiler costs. These checked
interfaces do not yet infer resource proofs for arbitrary native blocks.

The same consumer's `choosePrepend_execute` crosses an actual native conditional
and joins its selected List result into a common allocating call. It preserves
both original lists and the actual final heap, proves exact cursor growth of
nine words on the true path and six on the false path, and gives the complete
compiler-derived invocation count. The shared arena rules and proof pass compose
assignments, sequencing and conditionals with the existing call rules. Join-slot
initialization and copies are charged, but the unselected branch is not executed
or counted. Callee resource proofs and the selected path's capacity remain
explicit; no new interpreter or per-consumer register proof is introduced.

The [allocating-fold consumer](../../Examples/Language/LinkedListFoldAllocation.lean)
uses that contract-based rule for the actual generated `NativeLists.reverseAppend`
wrapper. Its selected `ListReducer.push` executes the real cons operation; the
existing generic fold resource proof sums its three-word allocation allowance
and constant compiler-derived callback cost. The same halted wrapper returns
`values.reverse ++ tail`, retains both original list observations and has a
full size-only affine invocation bound. Its sufficient internal call depth is
three, independent of list length; its final cursor is bounded by the initial
cursor plus `3 * values.length`. Input loading, word and code/stack/arena
conditions remain explicit. This is a cumulative fresh-allocation bound, not
an exact peak-live-space theorem. Correctness uses the generated refinement and
the ordinary reverse/append equation, with no repeated source loop induction.
The checked [structural arena proof pass](../../Complexity/Computability/Ram/Compiler/Language/Arena/Tactic.lean)
now reads the actual call/let/return statements and composes their existing
execution, readiness and cost rules. Both allocating consumers, including their
`prepend` and `push` constructor wrappers, no longer construct `Args`/`EnvFits`,
relocate callee proofs or build operational return continuations by hand.
Exact calls consume a measured callee; contract calls consume independent source
totality, resources and a bound. Imported function identity is recovered from
the actual call and its supplied table embedding, without opening callee bodies.
The generic contract form keeps mathematical resource indices explicit: they
cannot be reconstructed from raw list handles. The shared
[`List.Fold.arenaMeasured_of_ready`](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/Measured.lean)
entry now exposes the existing fold proof in ordinary mathematical/source
arguments. `reverseAppend` consumes its actual measured execution directly,
without assembling `functionPre`, a resource-index tuple or separate wrapper
totality/resource/cost contracts. Callback correctness, admissibility, value
ranges and remaining capacity remain supplied proofs. `reverseAppend` and
`reverseSum` no longer supply callback time certificates to obtain these
execution/space observations. Their independent structural cost proofs still
consume those certificates and apply to the same execution; the older bounded
`arenaMeasured` interface delegates to the new entry and adds that cost proof.
`ArenaMeasured` only packages existing witnesses; there is no new
interpreter or pricing model. The `measured using` call form retains those
observations directly, including across imports. `with_spec` attaches an
independent source specification to the same execution. The existing
`reverseAppend`, `reverse` and `reverseSum` resource proofs now compose these
certificates without unpacking and rebuilding execution/readiness/cost witnesses;
their final RAM publication uses the same measured proof directly. The old
ready/cost entry points retain their signatures through a shared extraction rule.
The shared allocating-loop cost rule below bounds actual executions. The
corresponding readiness rule now composes supplied guard/body proofs at changing
cursors. Automatically finding their range/capacity invariants, recursive
contracts and further operation resource adapters remains follow-up work.

`NativeViews.replaceHead` now joins the same actual Uncons call, optional-payload
match and allocating constructor. Its checked `replaceHead_execute_le` returns
`replacement :: values.tail`, preserves the original List observation and advances
the cursor by three words. Its full invocation bound is independent of list
length and includes node inspection, branch/payload/join copies and outer-call
overhead. The structural pass propagates actual selected-branch equations and
callee result ranges; the consumer supplies no manual raw-option cases or
register proof. `replaceHeadCost` now infers a uniform structural budget from
the actual body and two supplied callee certificates. `StmtArenaCostBound`
bounds the same actual arena cost, so publication applies that certificate
without a handwritten call-table or field-count formula. `prependCost` and
`prependPairCost` similarly infer the two straight-line constructor wrappers'
budgets while retaining their separately proved exact execution counts.
The shared `ArenaMeasured.execute_le` combines a measured body, its structural
bound and an independent `FunctionTotal` specification in one halted outcome,
transporting heap/value/cursor observations and adding invocation overhead once.
Mathematical correctness does not acquire a cost premise. Actual callee readiness,
word ranges, capacity and certificate selection remain supplied.
`ArenaMeasured.execute_eq` instead retains a measured exact count, publishing the
same specification and observations with exact body and invocation accounting.
The existing `prependPair` and selected-branch `choosePrepend` consumers use it
without unpacking execution witnesses or repeating final-heap transport.

The [indexed arena call rules](../../Complexity/Computability/Ram/Compiler/Language/Arena/CostBound/Call.lean)
select an existing callee bound at a mathematical input index, checking its actual
arguments and entry-heap precondition. The structural cost pass accepts
`certificate at index via embedding`; it does not infer a List from its root or
guess an input-dependent price. Adding `using specification` reuses an existing
`FunctionTotal` postcondition at the actual returned value and heap. This lets a
later call use the represented result as its mathematical cost index, rather than
bound impossible outcomes. The general `_le` rules additionally accept a
result-dependent continuation budget and a proved combining inequality; that
mathematical inequality is not inferred by the structural pass. The shared
[allocating-loop rule](../../Complexity/Computability/Ram/Compiler/Language/Arena/CostBound/Loop.lean)
uses an author-supplied ghost index, invariant and potential over the actual states.
It includes false exits and early returns, retaining the actual changing heaps
and cursor endpoints. It bounds an already given execution, not its termination.

The [indexed readiness rule](../../Complexity/Computability/Ram/Compiler/Language/Arena/Loop.lean)
likewise follows an existing successful finite source loop, but requires no time
potential. Its invariant carries a mathematical index and the actual arena
cursor. Actual guard and body endpoints are connected internally; normal rounds
choose a next index, and early returns retain their own postcondition. It does
not restrict allocating rounds to a fixed cursor. The
[fold readiness proof](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/Ready.lean)
uses the existing source `loop_total`, callback resources and accumulated
reservation to instantiate this rule, retaining ranges and shared-tail
observations at the actual new heap. No second list/termination induction or
callback time bound is required. This is a reusable proof rule, not automatic
invariant discovery or a peak-live-space result.

The [fold cost proof](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/CostBound.lean)
uses this rule and the existing source iteration postcondition. Its
`functionCostBound_of_actual` needs mathematical admissibility, accumulator
representation and List contents, but no separate resource contract, word-range
proof or spare-capacity premise. Those remain necessary when constructing a
ready execution. The compatibility `functionCostBound` delegates to this proof;
it no longer constructs a comparison traversal at cursor zero.
`pushCost` and length-indexed `reverseAppendCost` now infer the callback and native
wrapper costs from their actual bodies and existing callee certificates. The
ordinary reverse/append equation, affine invocation bound and three-word-per-head
allocation allowance are unchanged. Both folds' constant-callback envelopes
reuse `linearFunctionBound` and `functionBound_const`; traversal coefficients
belong to the shared library. General potential discovery, readiness inference
and arbitrary result-dependent budget comparisons remain mathematical work.

The [allocation-then-traversal consumer](../../Examples/Language/LinkedListComposition.lean)
connects the existing `NativeLists.reverseSum` to a complete RAM invocation.
Its first call allocates the real reversed List; the second traverses the actual
returned root, using the first call's generated refinement in its cost proof.
`reverseSumCost` infers the wrapper's bound from supplied callee certificates.
Its full invocation envelope is proved affine in length and `O(length)` using
mathlib's `IsBigO`, without restating compiler coefficients in the consumer.
The halted outcome returns `values.sum`, retains the original List in its actual
final heap, and has cursor at most the initial cursor plus `3 * values.length`.
The second fold allocates nothing. A final-sum range supplies every addition
range; code, stack and arena conditions remain explicit. The sufficient internal
depth is five, independent of list length. Both traversals and the outer
initialization/call/return/halt are charged; input loading and reclamation are not
claimed. No callback or source traversal is implemented or proved a second time.

The [typed-join RAM consumer](../../Examples/Language/LinkedListViewsCompiled.lean)
uses the same inferred bounds and publication rule. `headOr_execute_le` returns
`values.head?.getD fallback` and preserves the entire heap and cursor.
`inspectOrPrepend_execute_le` returns its represented optional head/tail and List
together, retains the original List, and advances the cursor by three words only
on the true branch, with no growth on the false branch. Both bound the complete
preloaded invocation, including actual result-slot initialization and field copies.
Their uniform instruction bounds do not assert an exact branch-dependent count
or remove the real launch and selected-path capacity conditions.

The [compiled native consumer](../../Examples/Language/LinkedListCompiled.lean)
now reaches the actual `Native.sumFrom` wrapper's halted RAM result, not merely
the separately runnable fold operation. A bound on `initial + values.sum`
supplies every intermediate addition range. Shared read-only bridges reuse
the existing call-realizability and cost tactics; the resulting bound retains
the wrapper's own call, return, initialization and outer halt. Source correctness
and exact heap preservation still have no word-range or time-budget premise.
The [ordinary-parameter resource interface](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/Native.lean)
now constructs the fold's environment and representation index and supplies
the zero-growth arena-to-fixed conversion. The consumer provides mathematical
prefix admissibility, ranges and existing callback resource facts; it no longer
repeats that generic environment/arena transport. This is not automatic resource
inference for arbitrary native declarations. The additional `sumPair`, `sumTwice`
and `sumWithPrepended` consumers have checked correspondence, but not yet their
own published RAM bounds. The allocating `reverseAppend` wrapper is covered
above, and `reverseSum` has the complete invocation bound just described;
`reverseWithHead` does not yet have its own published RAM theorem.

## Invocation and automation interfaces

`choosePrepend_execute` connects that same conditional wrapper to a halted RAM
invocation. It retains both original List observations and proves exact cursor
growth of nine words on the true path and six on the false path. Its exact count
includes actual calls, branch and join operations, the common continuation,
initialization and outer call/return/halt. The common arena proof pass composes
these statements from supplied callee costs; the consumer does not build
register or lexical-environment proofs. Word and code/stack/arena conditions
remain explicit, and input loading is outside the count.

`replaceHead_execute_le` connects that same declaration to a halted RAM result.
It retains the original list, advances the arena cursor by exactly three words
and bounds the full invocation independently of list length. The bound includes
the actual root test and possible node read, payload and join copies, constructor
call and enclosing initialization/call/return/halt. Existing List and heap
representation supply read success and payload ranges; the structural arena pass
propagates the selected Option branch and its returned ranges to the later call.
Word, code/stack and arena capacity remain explicit, with input loading excluded.
`ram_source_arena_cost` now infers `replaceHeadCost` from the actual body and
two supplied callee certificates. Its `StmtArenaCostBound` certificate applies
directly to the same measured execution; no call-table or field-count formula
is handwritten in this wrapper. The inferred `prependCost` and `prependPairCost`
also replace the two straight-line wrappers' formulas while preserving their
separately proved exact execution counts. The shared `ArenaMeasured.execute_le`
combines a measured body, its structural bound and an independent `FunctionTotal`
specification, retaining one actual outcome and adding invocation overhead once.
The mathematical specification needs no cost premise. Actual callee readiness,
certificate selection, ranges and capacity remain explicit. Other wrapper budgets,
dependent bounds and allocating loops are not automatically inferred by this fragment.

The typed-join RAM consumer uses these same interfaces. `headOr_execute_le`
returns `values.head?.getD fallback` with unchanged heap and cursor.
`inspectOrPrepend_execute_le` returns the represented optional head/tail together
with a List, retaining the original List observation and allocating three words
only on its true path. The false path has no cursor growth. Their uniform full
invocation bounds include actual join initialization and field copies; they are
not exact branch-dependent instruction counts. Input loading stays outside the
boundary, and real launch and selected-path capacity conditions remain required.

The compiled `Native.sumFrom` consumer uses those generated declarations and
the existing call proofs to reach the actual wrapper's halted RAM result.
Its ordinary final-sum range condition bounds all intermediate additions, and
its cost includes the wrapper and outer invocation rather than only the imported
fold body. The same source heap is retained. Shared ordinary-parameter fold
interfaces now supply argument-environment, representation-index and zero-growth
resource transport. The consumer retains its mathematical prefix-admissibility
and range proofs, callback resource facts and wrapper call composition. This is
not automatic resource inference for arbitrary native declarations.

The `prepend_execute` theorem in `Examples/Language/LinkedListAllocation.lean`
covers the actual generated allocating wrapper as well. Its shared
constructor-call bridge transports the already measured cons through the
program embedding and existing call/return rules.
The complete count includes the wrapper and outer invocation, not just the
standalone constructor. The same halted result retains the exact new root and
heap, the old tail's contents and a cursor increase of three words. Launch
conditions supply code/stack, rooted input and finite-word facts; the extra arena
capacity is independent of tail length. `prependPair_execute` composes two real
calls to that same generated `prepend`, giving an exact six-word cursor increase
and complete invocation count while retaining the shared old tail. The public
`ArenaExecutionCost.call_measuredOfEq` rule composes those exact observations;
`FunctionArenaResources.call_measuredOfEq` instead consumes independent source
correctness, resource and cost contracts. Both retain the actual intermediate
heap and cursor and charge the existing compiler's call overhead. Sequential
calls reuse the caller depth. These are reusable checked composition rules,
not automatic resource inference for native blocks.

`Examples/Language/LinkedListFoldAllocation.lean` checks the actual generated
`NativeLists.reverseAppend` wrapper through the same halted runner. The fold
invokes the real allocating `ListReducer.push`, and the shared resource rules
derive a full affine instruction bound and a final cursor at most the initial
cursor plus `3 * values.length`. Both original lists remain observable, even
when they share tails. The sufficient internal call depth is three and does
not grow with list length. The theorem counts the wrapper, all callback calls,
initializations and outer call/return/halt; input loading remains separate.
It gives a sufficient fresh-allocation bound, not exact peak live storage.

The checked `Arena.Tactic` pass now constructs that mechanical call/let/return
proof from the actual source body. `ArenaMeasured` is a thin proposition over
the existing execution, readiness and exact compiler count; its postcondition
can retain exact results or upper bounds. `ram_source_arena_step` handles
primitive bindings and returns, stopping at calls. `ram_source_arena_call exact
using cost` consumes an actual callee cost witness. The measured form composes
a returning `ArenaMeasured` directly; the indexed contract form consumes
independent source totality, resource and cost contracts. All accept
`via embedding` for imports. The actual arguments and continuation come from
the statement, and imported function identity comes from its table map.
For a known returned control, Lean's equality elimination removes the matching
existential result packaging. Unresolved mathematical cursor/cost comparisons
remain explicit; automatic reflexivity does not unfold arbitrary cost formulas.

The measured form can pause before the continuation with
`as finish value cursor steps observed fits`, before an optional `via embedding`.
These are the six binders of the existing call rule, not decoded mathematical
values or a new execution. This permits preparing one result-dependent callee
certificate before `ram_source_arena_step` splits a subsequent match. The
`replaceHead` consumer uses its actual returned tail this way; omitting `as`
preserves the automatic structural pass. Unresolved argument-range premises
remain proof obligations.

The `prependPair` and `reverseAppend` migrations include the leaf `prepend` and
`push` wrappers: no hand-written `Args`/`EnvFits`, import transport or operational
return continuation remains in those consumers. `List.Cons.ready_cost` provides
the original constructor proof in ordinary head/tail arguments, not a new
constructor implementation. `List.Fold.arenaMeasured_of_ready` exposes the existing
fold entry in ordinary accumulator/list/root arguments without a callback time
bound. It retains the actual count and allocation-cursor bound; independent
cost certificates can be applied to that same execution later. `reverseAppend` now
consumes that actual execution through the measured-call form; it no longer
builds a resource-index tuple, `functionPre`, or separate wrapper contracts.
Both its resource proof and `reverseSum`'s post-allocation traversal use this
resource-only entry. Their separate instruction-bound proofs retain the callback
cost certificates. The older bounded `arenaMeasured` interface remains available.
The callback contracts, admissibility, numerical ranges, remaining capacity and
final comparisons stay explicit. The generic contract-call form remains useful
for other indexed operations; the pass does not decode mathematical lists from
handles or infer arbitrary loop/recursion bounds. Automatic selection of further
ordinary-parameter adapters and the remaining loop-view/local conversions are
still open.
