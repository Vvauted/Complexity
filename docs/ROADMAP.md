# Roadmap

Write one executable program, state its correctness with ordinary Lean mathematics,
and derive its complexity without reopening the machine implementation.
A pleasant DSL, reusable proofs and proof automation are parts of the same goal.

This roadmap is driven by the existing samples, not by the number of interfaces
or lemmas in the repository. [Design](DESIGN.md) records semantic boundaries;
[literature notes](LITERATURE.md) record what we take from other work.

## What the samples actually establish

The checked function path supports word, borrowed-array and genuine `Unit`
results, typed mathematical contracts, budget-free correctness, separate compiled
costs, and ordinary executable value equations. The existing samples exercise
these through the actual compiler and runner, not syntax or backend lemmas alone.

| Consumer | What works | What still costs the proof author too much |
| --- | --- | --- |
| [Factorial](../Examples/Ram/Factorial.lean), [FunctionRun](../Examples/Ram/FunctionRun.lean) | Ordinary induction proves correctness and a single exact-cost recurrence. The upper bound and measured endpoint reuse these proofs; executable values rewrite to mathlib factorial. | Publishing the runtime equation still assembles source observations and justified word/stack conditions; general state-dependent exact composition needs more rules. |
| [LocalBindings](../Examples/Ram/LocalBindings.lean), [ArrayFold](../Examples/Ram/ArrayFold.lean) | Calls reuse helper correctness; shared traversal proves the list fold. Uniform and actual element/prefix-dependent cost rules are available, exercised by an adapter around the existing factorial. | The caller still supplies the mathematical update, element domain and accumulator invariant. Mutable or richer-accumulator traversals are not covered by this read-only scalar rule. |
| [ArraySlice](../Examples/Ram/ArraySlice.lean), [ArraySliceProperties](../Examples/Ram/ArraySliceProperties.lean) | A real function returns a typed borrowed slice to another compiled call; ordinary `List.drop`, `take`, and sum identities apply. Its time continuation receives that reference directly and bounds summation using its actual length. | The author still selects the typed input, transports representation facts and justifies the mathematical continuation bound. |
| [LowerBound](../Examples/Ram/LowerBound.lean) | A named binary-search function has budget-free total correctness, an ordinary executable `List.findIdx` equation, and a separate full-call logarithmic bound. Shared-state restoration uses a common rule. | The implementation adapter still proves local-slot separation and initialization; the short client theorem does not remove that work. |
| [Merge](../Examples/Ram/Merge.lean) | A three-array `Unit` function exposes its actual destination as standard `List.merge`, preserves both sources and has an independent full-call linear bound. Existing call automation reuses one verified core loop. | The typed entry is a real wrapper call with additional cost; clients still prove their genuine extent and aliasing conditions. |
| [Merge sort](../Examples/Ram/MergeSort.lean) | A real two-array `Unit` declaration recursively calls itself, merge and copy. Ordinary length induction composes shared slice/reassembly rules; actual output has a sorted-permutation and `StateM` specification, with a separate full-run `n log n` reserve. Correctness and time calls restore caller bindings; the time rule derives each remaining reserve. | Correctness and time proofs still repeat stage composition. The author supplies the whole-branch reserve, recursive capacity and array facts; these must not be confused with automatically derived call accounting. |
| [FunctionComposition](../Examples/Ram/FunctionComposition.lean), [its time proof](../Examples/Ram/FunctionCompositionTime.lean) | Copy and sum are real imported source calls, with independently reusable correctness and time proofs. | Clients transport contracts through imports, rebuild representations, unpack register preservation, and choose numeric continuation reserves. |
| [GraphDegree](../Examples/Ram/GraphDegree.lean) | A client can transfer an implemented list sum to a mathlib graph property. | This assumes represented graph data; it is not a graph loader or compilation of arbitrary Lean predicates. |

The diagnosis is not that mathematical statements are impossible. They already
work. The missing step is making their implementation proofs and separate cost
proofs consistently compositional and source-facing.

## Four questions for every proposed change

### 1. Are public proof rules and automation doing the repetitive work?

A public rule should remove repeated work from an existing consumer. Parameter
binding, return binding, scope restoration, import relocation and routine framing
belong in reusable rules. Automation should apply those proved rules and leave
readable mathematical goals.

The author still supplies genuine invariants, recursive measures, callee
contracts, range/aliasing facts, and recurrences or potentials. Hiding these goals,
weakening the input domain, or replacing them with a blanket execution premise
does not improve proof automation.

Prefer compositional rules for calls, sequencing, branches, loops and recursion
over another recognizer for one exact sample AST. Retain focused shortcuts where
they are useful, but do not make a tiny syntactic variation require an entirely
new correctness proof. Exact costs and upper bounds should share the same source
decomposition rather than forcing clients back to separate execution-tree proofs.

### 2. Are we actually reusing Lean, Std, Batteries and mathlib?

Already reused: `Part`, ordinary lists and vectors, `StateM` and `Std.Do.Triple`,
standard induction, `Set.EqOn` for unchanged locals, asymptotic relations, and
mathlib's Akra–Bazzi machinery.
Do not build replacements for these.

The word-sum algebra in [Array/Sum](../Complexity/Computability/Ram/Array/Sum.lean)
now reuses `List.sum_eq_foldl` and standard sum identities through one
encoding/modular-arithmetic bridge. Typed result decoding similarly reuses
standard list-length and element facts. Do not maintain parallel collections of
generic list proofs; preserve the project-specific representation bridge.

Memory-to-list representation, source-to-target simulation and compiler-derived
costs are necessary project-specific bridges; an upstream `List` or `Part`
lemma cannot replace them. Before adding a generic lemma, search the pinned
dependencies and record a concrete reason if a small extension is still needed.
Do not expand dependency scope merely to advertise reuse; CSLib is not required.

### 3. What should writing a proof feel like?

The author writes a function with typed parameters, local bindings, calls and
returns. Its correctness proof follows the algorithm: ordinary induction,
a loop invariant, or composition of known operation contracts. Its cost proof
follows the same decomposition, leaving sums, inequalities and recurrences.

A proof about a client should not mention register numbers, stack save/restore
instructions, raw code layout, generated function-table offsets, or a manually
reconstructed execution tree. Backend authors prove those facts once.

Proving an implementation and using its theorem are different tasks. Both matter:
a short mathematical client theorem does not excuse a large, repetitive
implementation proof hidden in another sample file.

### 4. Can correctness be stated like an ordinary Lean proposition?

Yes. The existing executable factorial equality and slice identities demonstrate
this. The target includes both value equations and relational specifications;
sorting need not be specified by implementing a second sorting algorithm.

These are schematic proposition shapes, not additional implemented APIs:

```text
pure result:       admissible x → implementedFunction x = mathematicalValue x
relational result: admissible x → property x (implementedFunction x)
mutable result:    represented input entry →
                     let (result, finish) := implementedFunction input entry
                     resultProperty input result ∧ represented output finish ∧ frame entry finish
separate cost:     admissible x → costOfThatInvocation x ≤ bound x
```

Admissibility must describe the intended legal inputs and real representation,
overflow and capacity conditions. A named condition may package them; it must not
hide an unproved halt assumption or discard inconvenient legal inputs.
Once termination follows from those conditions, ordinary application should not
require the client to assemble a machine trace or choose a time bound.

A pure result need not display streams or a heap. Hiding shared state requires
proving independence and preservation, not just choosing empty input.
Effectful programs may naturally use stateful/Hoare specifications.
Heap-backed arrays are currently references with list representations, not an
implemented `List → List` loader. Conversions and allocation need real programs
and their own costs before an end-to-end list API can claim them.

## CALF as a guide, not a label

[CALF](https://arxiv.org/abs/2107.04663) distinguishes values from computations
and behavioral equality from cost-sensitive reasoning. Its phase discipline
prevents cost information from affecting observable behavior. These are stronger
ideas than merely storing a pair of a result and a number.

For this library, make the corresponding obligations concrete:

- Typed result and state observations describe the same executable declaration
  as its cost observation. Correctness and termination do not depend on a
  proposed bound.
- The source program cannot inspect proof budgets or the measured step counter.
  Erasing measurement must preserve results and effects; measuring a terminating
  invocation must not choose a different execution.
- Behavioral equality permits reuse of mathematical properties, not transport of
  a runtime bound between different algorithms. A separate cost/refinement theorem
  is required.
- Cost composition follows actual intermediate values and effects. A call's
  returned array or updated state can determine the next call's bound.
- Local costs and calling overhead come from proved compiled executions. No
  unchecked `tick`, host callback or bulk operation may assign itself a price.

The existing erasure, determinism and result/count correspondence theorems support
this direction. They are not a formalization of CALF's modal type theory or its
internal noninterference metatheorem. Extend the typed proof interface on that
existing semantics; do not start a disconnected interpreter or a second program
whose connection to the executable remains the user's burden.

[Refinement with Time](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.20)
motivates compositional representation and cost rules.
[Decalf](https://arxiv.org/abs/2307.05938) is a useful warning that effects need
cost comparisons which retain behavior, rather than assuming every computation
has a separate pure scalar cost formula. These motivate the design; our RAM
adequacy claims must still be proved here.

## Priority 1: typed function path — checked foundation

The multi-field path now covers source semantics, both
compilers, checked arities, executable calls, DSL signatures, imported signatures,
typed observations and contracts. Word, borrowed array and `Unit` results
use actual returned fields from the same callee execution.

`TypedFunctionContract` exposes typed arguments and results, not only generated
`eval`/`apply` entry points. Shared semantic and executable projection theorems
remove per-client field-length and decoding proofs. This is a thin view of the
one declared implementation, not another program container.

`ram_total_vc` also starts these typed contracts through their existing `of_wp`
rule. The callable merge uses it and `ram_total_apply` to leave only its array
premises and result representation; no separate typed verification tactic is needed.

**Checked evidence:** the slice consumer returns a borrowed array which another
function passes to imported sum. Copy genuinely returns `Unit` and preserves its
heap effects in copy-then-sum. Both have mathematical contracts and independent
compiled costs without a stream driver, fabricated result fields or host-side
sequencing masquerading as one compiled program. Scalar and recursive consumers,
the full library, examples and manual pass on the designated server.

This establishes the typed path, not the final proof experience. A dedicated
declaration-generated binding set now removes repeated argument-builder,
lookup and static arity/local-count facts, including imports. Slice's reduced
call proof exercises it. Calls still need explicit typed-input selection and
mathematical representation reasoning; no encoding is inverted by guesswork.

A `Unit` value alone is not an observation of mutation or execution steps.
Use the same invocation's state/count interface to observe those effects;
a source-language `Unit` call still executes its body and calling convention.

## Priority 2: share source-facing correctness and cost decomposition

Build on the existing total-correctness and measured-execution rules.

**Checked foundation:** `TimeExact` provides conditional exact-count composition
over the original measured semantics. Factorial now uses one ordinary cost
induction; its upper bound and measured body execution are projections, not
separate execution-tree proofs. `ram_run_bound` composes the actual runtime
bridge and proved outer-overhead arithmetic for copy, slice and copy-then-sum.
`ram_run_eq` provides the corresponding exact-count convenience, used by the
actual factorial and array-sum applications without local call-length rewrites.

The uniform `ForIn.function_timeBound` needs no exact helper count or totality.
The separate `function_timeBound_of_step` sums work at actual elements and prefix
accumulators, using a read-only correctness contract on admitted inputs. The
shared traversal rule now requires the step only when its guard is true; an empty
endpoint does not impose correctness of an unexecuted call. The existing
factorial adapter supplies real input-dependent cost, an explicit element bound
and sufficient recursive capacity. Standard list operations supply the sum;
there is one small generic prefix-sum identity, not a new cost monad.

`TimeBound.while_div` now specializes the existing linear-loop rule using
ordinary `Nat.clog` lemmas. Bit length and named lower-bound search both use it
instead of repeating logarithmic-potential arithmetic. Search shares one
budget-free interval-halving iteration relation between termination and the
separate time proof. The costs still include every compiled guard and back-edge;
the shared rule does not assign an abstract constant price to the whole loop.

**Checked local-binding step:** `State.LocalFrame` packages unchanged shared
state with mathlib's `Set.EqOn` on unaffected locals. The expression-fold adapter
proves parameter/local separation once and transports the same parameter facts
through initialization, element loading and cursor advance. Search and both fold
adapters reuse `restore_eq_of_shared` at return. Function entry is still a real
change of register environment: the local frame starts after `entry.enter args`.
Neither endpoint equality nor discarded locals erase executed assignment costs.

This is an implementation-side bridge, not automatic scope inference or a net
reduction in every proof's length. LocalBindings already composes its calls in
a few lines; search's two single-register reads remain simpler without a set
frame. Do not migrate such proofs just to demonstrate the new interface. The
remaining `Nodup`/register-role adapter and expression meaning are still explicit.

**Remaining work:**

- Make local-block proofs follow the source structure without exposing numeric
  slots. Search's scoped midpoint must remain local to its loop body; exporting
  it as a function-level variable would misrepresent the language's scope.
  Reuse `TotalWP.while_variant`, ordinary-model `Refines.while_wellFounded`,
  and existing statement rules. Build on the checked parameter-preservation
  bridge when a real local-block proof still repeats this work;
  do not replace the loop framework or accumulate whole-sample AST recognizers.
  A small binder tactic is worthwhile only if the resulting proof is actually
  clearer than the existing substitution rules.
- Extend the exact-cost interface beyond state-independent continuations.
  Correctness, exact costs and upper bounds should share source-facing call and
  sequence decomposition even when a returned value determines later work.
  Keep cost equations proved, not annotations accepted by the compiler.
  Do this when an exact-count consumer needs it: the slice currently needs an
  upper bound, already covered by the typed continuation rule, not another
  exact-cost wrapper with no client.
- Simplify other recursive consumers with these rules before proposing another
  recursion framework. Retain a stronger body invariant only where actually
  needed; do not infer discarded callee locals from restored caller state.
- Simplify representation transport in effectful typed continuations.
  The restored call rules now carry actual effects without register equalities;
  merge sort uses the default remaining reserve and slice retains an explicit
  bound depending on `window.length`. Neither rule decodes a guessed input or
  changes the execution. Repeated multi-buffer stage composition remains work;
  its genuine mathematical facts stay explicit.

**Evidence of completion:** `LocalBindings`, factorial, `ArrayFold`, and
copy-then-sum use the common rules. Their algorithmic proofs retain only relevant
invariants, contracts and mathematical cost arguments; neither exact-count nor
upper-bound clients reconstruct ABI blocks or measured execution trees.
The data-dependent factorial fold meets the varying-helper part of that evidence;
it does not establish arbitrary mutation or richer accumulator support. A
conditional time bound does not become monotone in allowed call depth without
justification; this consumer transfers it using an actual execution and determinism.

## Priority 3: make data-operation contracts compose naturally

Use ordinary list/array/graph properties at the mathematical boundary and reuse
the existing `StateM` / `Std.Do` interfaces where they help.

- Imported operation contracts should transport lookup, argument/result binding
  and routine frames without clients rebuilding those facts.
- Return useful representation postconditions directly: copying produces a
  represented destination; slicing produces a represented borrowed reference.
  Preserve range, overlap and mutation conditions.
- Base function-level `StateM` bridges on returned values and shared effects.
  Reconstructing values from destination registers is a lower-level observation,
  not the preferred interface for proving ordinary functions.
- Extend traversal and mutation rules through actual consumers, including
  multiple live arrays and richer accumulators. Do not add containers merely to
  increase the library's feature count.
- Keep borrowed descriptors, allocated storage, mathematical views and actual
  data conversion distinct. Only implement loaders/allocation when their
  semantics and costs can be included in the claimed interface.

**Evidence of completion:** the returned-slice and copy-then-sum proofs need no
callee implementation details. The existing merge-sort proof already reuses
operation contracts at a lower level; its algorithmic proof should instead
compose named parameters, results and array representations without restating
call ASTs or assembling register states. Subsequent list/graph properties use
upstream mathematics.

Merge sort now connects its existing `sortState` to the actual new function's
contents using the checked `applyState` bridge. This is a contents-level
refinement: the RAM function also changes scratch storage, whose final contents
need not be part of the ordinary list model. Adding another wrapper around this
equation would not shorten its multi-buffer binding proof. Copy likewise already
has a direct `Unit`/shared-state specification; no duplicate stateful model is needed.

**Checked merge step:** the named core shares the existing merge loop, and the
typed `merge(left : array, right : array, destination : array) : Unit` makes a
real call to it. The destination equation is standard `List.merge`; sortedness
is needed only for the sorted-permutation corollary. Both sources survive and
may overlap each other. The destination view has exactly the combined length
and is disjoint from each source. This typed length is word-representable;
the raw core retains its broader domain of two separately representable counts.
The actual typed invocation has bound `34 * (xs.length + ys.length) + 122`,
including both calls, returns and halt. Neither storage allocation nor loading
is claimed. A larger allocated buffer can supply a contained destination view.

**Checked representation step:** `ArrayAt.reassemble_prefix_of_frame_two` and
`reassemble_suffix_of_frame_two` now carry the unchanged half across an operation
on the other half and a contained scratch view. Both existing `after_left` and
`after_right` use these public rules. They mention neither registers nor return
fields, permit unequal source/scratch lengths, and retain empty endpoint cases.
The old recursive adapters still bind their actual operands; this extraction
does not claim those adapters are already source-facing.

**Checked typed recursive correctness:** the new two-array, `Unit`-returning
declaration uses ordinary length induction whose callable hypothesis covers all
input-reference pairs. Public `Stages` rules split the arrays, preserve the
unchanged half across each actual recursive call, refresh scratch contents, and
prepare merge. Typed contract relocation reuses the existing import embedding;
larger call-depth capacities preserve the same budget-free correctness.
`Function.sort_contents`, `sort_sorted` and `sort_stateM` observe this new
compiled declaration, not the old three-parameter sort or a host sorting call.
Empty arrays, odd sizes and duplicates remain in the domain.

**Checked independent cost:** the same declaration has body bound
`Recurrence.balancedBudget 4 227 n`; its taken branch charges a nonrecursive
`53 * n + 348`, including descriptor assignments, recursive call blocks, merge
and copy. `Function.runTotal_steps_le` adds the actual outer invocation and halt,
giving `bodyBudget n + 81`. The existing balanced recurrence and mathlib `IsBigO`
prove the reserve's `n log n` growth. This is a bound, not an exact count or a
comparison-only model. The separate time induction handles every sufficient
call depth directly; it does not assume conditional time bounds are monotone
in that capacity. Each fixed-width execution still has real code/stack and
representation premises, and no allocation or loading cost is claimed.

**Checked call-composition improvement:** `TypedFunctionContract.wp_call_restored`
passes the actual shared effects with caller bindings already restored. The
three typed sort calls use it and no longer accumulate register equalities.
It reuses the existing call rule, retains ordered return-field assignment, and
does not change the tactic's global rule selection or gather all local facts.
Mathematical names such as the midpoint stay opaque in continuations; expanding
them into word-arithmetic expressions everywhere makes list reasoning needlessly
difficult. The migrated proof avoids that global unfolding.

**Checked time-call improvement:** `call_seq_typed_restored_at` provides the same
binding behavior for independent time proofs. `call_seq_typed_remaining_at`
derives the continuation reserve by subtracting the proved complete call bound,
with an explicit affordability premise. Merge sort's three typed calls use
`ram_time_apply correct time on input`; they no longer choose intermediate
numeric reserves or accumulate register equalities. `ram_time_vc` normalizes the
compiled call-length terms in the reserve without unfolding callee bodies.
Slice retains an explicit `nextBound` depending on its actual returned length.
Both consumers retain their original execution and bounds.

This does not infer the algorithm's whole-branch bound or recurrence. The author
still proves that both children and the actual nonrecursive toll fit the proposed
reserve. Natural-number subtraction cannot justify overspending. Automation
handles lookup and argument equations; it does not repeatedly search a large
continuation or unfold mathematical names there while attempting those premises.

**Next proof-experience work:** migrate copy-then-sum's effectful call to the
existing typed/restored call rules before adding another interface. Its old proof
still unpacks preserved registers and chooses a continuation reserve by hand.
Then reassess repeated multi-buffer stage composition. Extract a shared rule only
when it removes work without hiding representation, mutation or capacity
obligations; do not add another recursion framework or whole-sample AST recognizer.

**Checked lower-bound step:** search is now a named callable function, with
ordinary endpoint initialization and a loop-scoped midpoint. Its shared interval
and exit proofs are register-parametric; the old binary-insertion specialization
remains usable. Budget-free termination uses interval decrease, correctness
reuses `LowerBoundSpec.eq_findIdx`, and the separate full-run bound is
`25 * Nat.clog 2 (xs.length + 1) + 69`. The additional initialization, call,
return and halt costs come from this actual function, not the old block.
The admitted data includes empty arrays and duplicates without an extra strict
array-endpoint condition. Normal execution still needs its genuine stack capacity.

This completes one source-to-runtime consumer, not the full high-level interface.
Its private binding adapter is a temporary localized cost to proof authors, not
a new public verification framework. Shared restoration is now factored out;
source-local layout and multi-buffer representation still need attention. Do not add dummy
parameters or whole-program renaming merely to preserve old numeric slots.

The language itself is also unfinished. Word, borrowed-array and `Unit` results,
with only end-of-function returns, are not a complete high-level programming
experience. Search's insertion index, including `xs.length`, is a legitimate
mathematical result, not evidence that it needs `Option` or early return.
Use an actual structured-result or early-exit consumer to justify those features.
Source lowering, correctness, costs and runtime observations must arrive together;
parser acceptance alone is not completion.

## Priority 4: publish mathematical statements once per declaration

Consolidate correctness-to-evaluation and correctness-to-execution bridges.
Generate or derive reusable declaration-level observations and named, justified
capacity conditions; do not introduce a third unrelated function container.

Keep `Part` for semantic partial observations and actual compiled application
for executable values. Pure clients should reuse plain value equations;
mutable clients should reuse result/state contracts. Separate time theorems must
continue to describe the identical invocation, including its actual outer
overhead, without feeding the bound to the implementation.

**Evidence of completion:** the factorial, slice and composition clients publish
ordinary equations/relations and independent time bounds without per-client
raw-code declarations, proof-only reference algorithms, or hand-extracted result
registers. Their real legal-input and representation assumptions remain visible.

**Checked value-projection step:** `LocalCompiler.Function.applyTyped_spec`
transfers a typed contract to any proved property of the actual returned value.
Lower-bound search and slice sum now use it without unpacking `FunctionExec` or
connecting returned fields by hand. Their remaining mathematical steps use
`LowerBoundSpec.eq_findIdx` and `wordSum_toNat`. The rule reuses the existing
`applyStateTyped_spec` and its value projection; it does not create another runner.
Discarding shared state from this conclusion does not prove that the execution
has no effects. Mutable clients keep the result/state interface.

The declaration-level application still carries justified input and capacity
conditions. Derive additional observation conveniences only when they remove
repeated client work; do not duplicate this bridge with a third function container.

## Later work and limits

The current cost is word-RAM transitions, not Lean interpreter wall time or bit
complexity. Uniform whole-problem statements must keep the original input domain,
encoding, width policy and size measure. Host preloading is not a proved loader.

Space needs a separate observation of live resources on the same execution.
A sufficient address-space bound is not peak live storage. Prove actual stack
liveness before advertising stack-space bounds, and allocation/reclamation
before claiming general live-heap space.

Cross-model complexity needs a costed simulation and justified bit/word encoding.
Do not let a catalog of complexity classes, extra machine models, or more generic
recurrence wrappers displace the proof-experience priorities above.

## Keep questioning the plan

Work in small consumer-driven steps: identify a painful proof, add or reuse the
public rule that removes it, check the consumer on the designated server, and
update the claim here. Keep in-progress work distinct from verified interfaces.

When a design choice is unclear, read the relevant sections of one or two primary
papers and compare their assumptions with ours. Record the decision and its limit
in the literature notes; a bibliography is not a deliverable by itself.
Revisit priorities when a sample exposes a missing premise, duplicated proof,
unaccounted operation or unusable interface. Do not preserve a design merely
because it is already implemented.

Use Lean's checks and the real samples. No separate audit framework, checksum
machinery or unrelated test scaffold is needed for this process.
