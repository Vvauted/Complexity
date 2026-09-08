# Roadmap

Write one executable program, state its correctness with ordinary Lean mathematics,
and derive its complexity without reopening the machine implementation.
A pleasant DSL, reusable proofs and proof automation are parts of the same goal.

The checked backend and mathematical observations already work. The main gap is
the experience of proving a new implementation: mutable loops and recursive
multi-buffer composition still expose too much source-state plumbing.
A short client theorem does not excuse that burden in an implementation module.

This is a plan, not a chronological list of completed lemmas.
[Design](DESIGN.md) records semantic boundaries, the
[manual](https://vvauted.github.io/Complexity/ComplexityDocs/Verification.html)
describes proof interfaces, and [literature notes](LITERATURE.md) record what we
take from primary papers.

## Four questions for every proposed change

### 1. Do public rules and automation remove repeated work?

Parameter and return binding, import relocation, scope restoration and routine
frames belong in shared rules. A proof should follow calls, sequencing, branches,
loops and recursion in the declared source. Small changes to a loop body should
not require a new whole-function AST adapter.

The author still supplies mathematical invariants, recursive measures, callee
contracts, range/aliasing facts, and recurrences or potentials. Automation should
leave those goals readable, not replace them with blanket execution premises or
weaken the admitted input domain.

### 2. Are we reusing Lean, Std, Batteries and mathlib?

Reuse ordinary lists, arrays, vectors, `Part`, `StateM`, `Std.Do.Triple`, induction,
`Set.EqOn`, asymptotic relations and mathlib's recurrence machinery.
Do not create parallel collections, monads or asymptotics libraries.

The current sum algebra uses upstream list sums through a word-encoding bridge.
Array mutation reuses list `take`, `drop`, `set` and map identities.
Local frames and static destination sets use ordinary mathlib sets.
Memory representation, compiler simulation and actual transition costs are
project-specific bridges; an upstream list theorem cannot replace them.

Search the pinned dependencies before adding generic mathematics. Add a small
extension only for a concrete missing fact. Keep dependency pins consistent;
CSLib is not needed for this direction.

### 3. What should proving an implementation feel like?

Write a function with typed parameters, lexical locals, calls and returns.
Prove its behavior by ordinary mathematical induction, a loop invariant, or
composition of operation contracts. Prove its cost using the same decomposition,
leaving sums, inequalities and recurrences.

A client proof should not mention numeric register slots, stack instructions,
generated function-table offsets, raw code layout or measured execution trees.
Backend authors establish those facts once. Both implementation proofs and
downstream mathematical uses must be pleasant; hiding boilerplate in a sample
adapter is not completion.

### 4. Can correctness look like an ordinary Lean proposition?

Yes: executable factorial equations, slice identities, `List.findIdx`, mapped
contents and sorted-permutation statements already demonstrate this.
A relational specification need not implement a second reference algorithm.

The intended proposition shapes are schematic, not new APIs:

```text
pure:      admissible x → implementedFunction x = mathematicalValue x
relation:  admissible x → property x (implementedFunction x)
mutation:  represented input entry →
             resultProperty result ∧ represented output finish ∧ frame entry finish
cost:      admissible x → costOfThatSameInvocation x ≤ bound x
```

Admissibility retains real representation, overflow and capacity conditions.
Normal termination must follow from those conditions without choosing a time
budget. Packaging them must not hide an unproved halt assumption.

A pure observation may omit heap and streams, but a purity claim requires
independence and preservation. Mutable programs naturally use result/state
contracts. A heap reference represented by a list is not an implemented
`List → List` loader; actual conversion and allocation require charged programs.

## Evidence from the existing samples

| Consumer | Checked end-to-end capability | Remaining burden |
| --- | --- | --- |
| [Factorial](../Examples/Ram/Factorial.lean), [FunctionRun](../Examples/Ram/FunctionRun.lean) | Ordinary induction proves behavior and one independent exact-cost recurrence; executable equations reuse mathlib factorial. | Publishing the runtime result still supplies genuine word and stack conditions. General value-dependent exact-cost continuation support needs a real consumer. |
| [LocalBindings](../Examples/Ram/LocalBindings.lean), [ArrayFold](../Examples/Ram/ArrayFold.lean) | Named calls and shared traversal yield `List.foldl`; the factorial helper exercises element/prefix-dependent costs. | The fold interface is read-only with a scalar accumulator, not arbitrary mutation or richer accumulator support. |
| [ArrayMap](../Examples/Ram/ArrayMap.lean) | Real helper calls and stores produce `List.map`; independent bounds cover the same compiled invocation. The indexed rule owns cursor/count progress. | The payload still relates source state to mathematical contents and a real user index. The operation template retains a fixed internal layout. |
| [ArraySlice](../Examples/Ram/ArraySlice.lean), [properties](../Examples/Ram/ArraySliceProperties.lean) | A real returned borrowed reference feeds another compiled call; its length controls the time continuation. | Typed-input selection and mathematical containment/representation facts remain explicit. |
| [LowerBound](../Examples/Ram/LowerBound.lean) | Named source directly composes shared loop rules, with budget-free termination, executable `List.findIdx` and a logarithmic full-call bound. | The invariant/initialization still use a register-role bridge. The loop-scoped midpoint is not a function-level binding. |
| [Merge](../Examples/Ram/Merge.lean) | A three-array `Unit` function yields `List.merge`, both preserved sources and an independent linear full-call bound. | The wrapper really calls the core and pays that overhead; extent and destination non-overlap remain premises. |
| [MergeSort](../Examples/Ram/MergeSort.lean) | A two-array declaration recursively calls itself, merge and copy. Length induction gives sorted-permutation and contents-level `StateM` specifications; the same invocation has an `n log n` bound. | Correctness and time still repeat some stage composition. Recursive capacity, the whole-branch reserve and multi-buffer facts are explicit. |
| [FunctionComposition](../Examples/Ram/FunctionComposition.lean), [time](../Examples/Ram/FunctionCompositionTime.lean) | Imported copy passes complete array representations to sum; call accounting derives the remaining reserve. | Import transport and genuine equal-length, range and disjointness premises remain. |
| [GraphDegree](../Examples/Ram/GraphDegree.lean) | An implemented sum transfers to a mathlib graph property. | Represented graph data is assumed; this is not a graph loader. |

All these claims concern the actual source/compiler/runtime path, not parser
acceptance or a mathematical replacement implementation. Existing source
programs, admitted domains and cost bounds must be preserved when simplifying
their proofs.

## Priority 1: make new mutable and scoped proofs source-facing

**Available foundation:** general `TotalWP.forIn` supports arbitrary bodies and
loop-head state invariants; its independent uniform time rule charges setup,
loads, cursor updates and control flow. `forIn_indexed` additionally maintains
the mathematical iteration number and private cursor/count relation internally.

Map supplies represented updated-prefix/unread-suffix contents, base/index
bindings and frame/I/O facts. `forIn_indexed_of_frame` lets its body prove only
the body-endpoint payload; one ordinary local-frame stability proof transports
it through private cursor setup and advance. The implementation no longer unfolds
those state updates or proves their arithmetic. The body still reads the current
heap and may change shared state. Semantic cursor preservation permits
write-then-restore; static destination exclusion handles the simpler case.

The map body composes the existing function-call WP, array-store contract and
assignment rule directly into its next mathematical invariant. It no longer
reconstructs a whole-body execution endpoint before proving the array result.
The underlying list identities remain upstream `take`, `drop`, `set` and `map`
reasoning; the operation still owns its fixed local layout.

`ram_total_store` now applies the existing array-store contract to the actual
leading store. Map supplies its mathematical array assertion, index and value;
it no longer repeats the address/value syntax or wraps the assertion around
local-register updates. The continuation receives `List.set` and the actual
outside-array frame. A changed heap still requires a current representation;
routine simplification does not transport an assertion through arbitrary effects.
The final index update and invariant implication remain explicit.

The actual source now uses `for i, x in xs`, with both binders immutable and
body-local. Its generated index initialization/increments give exactly the same
map function, so the existing mathematical result and compiled costs are retained.
This improves programming without inventing another local-reader record; the
operation's internal payload still uses a fixed register layout.

**In progress: source-directed verification conditions.** The same lowering now
retains intermediate lexical scopes and actual emitted fragments as proof-site
metadata. Previously only bindings visible at the function return survived.
This is necessary to distinguish a midpoint before/after its declaration and
inner shadowing, but metadata alone does not improve a correctness proof.
There is not yet a source-proof driver consuming these sites.

**Next work:**

- Keep removing repeated operation-level work using the existing WP goals before
  adding a whole-source proof driver. The store step demonstrates that actual
  operands can be inferred by unification; it does not need a second AST walk or
  lexical metadata. Scope metadata is needed for source-name visibility, not for
  every elementary proof operation.
- Connect these sites to existing WP decomposition, beginning with Map's actual
  named helper-call/store body. A proof cursor must accompany code continuations,
  not ordinary lookup, read-safety, representation or depth goals. Enter loop
  scopes only at their actual loaded/body entry; restore outer bindings on exit.
  Consume generated initialization and tail instructions rather than skipping
  them because they lack a source statement. Array-local initialization completes
  both real assignments before exposing the new descriptor.
- Use the actual goal's statement and returned values. Do not find a source site
  by scanning for an equal AST or re-elaborate an embedded `const(t)` in a new
  Lean scope. Introduce ordinary word/reference values from current bindings;
  after calls, transport heap representations only using their actual contracts.
  Restored caller registers do not imply an unchanged heap.
- The first concrete body should expose a helper postcondition followed by
  `List.set` and its frame, using the existing call and array-store rules. It
  should not reproduce `.var` slots, receiver updates or expression evaluation.
  Mathematical index ranges, Word/Nat correspondence, aliasing and the payload
  implication remain ordinary Lean obligations. A generated reader, a new
  whole-Map AST adapter or another `Refines`/`StateM` wrapper is not this milestone.
- Retain the concise scalar-fold and whole-operation contracts where they suffice.
  Rewriting all clients into a more general invariant is not itself an improvement.
  Multiple live mutable arrays and richer accumulators need a representation
  interface that preserves their actual ordered effects.
- The language supports word, borrowed-array and `Unit` results and end-of-function
  returns. Richer results and early exit remain unfinished. Select a genuine
  consumer before extending them, then provide lowering, correctness, cost and
  runtime observations together. Search returning its insertion index, including
  the endpoint, does not by itself require `Option`.

**Acceptance evidence:** the next genuinely different mutable body should reuse
the traversal mechanics while its proof contains the algorithm's mathematical
invariant and operations. Private layout changes should not force a new
algorithmic correctness argument. No uncharged host callback or array snapshot
may stand in for the body.

## Priority 2: share independent correctness and cost decomposition

**Available foundation:** typed call rules pass actual returned values and shared
effects with caller locals restored. `ram_total_apply` and `ram_time_apply`
reuse declaration-generated bindings. The time rule can derive a remaining
reserve after proving the complete compiled call fits, or accept an explicit
continuation bound depending on the actual returned value, as slice does.

The explicit-input `ram_total_apply contract on input` form follows the same
selective premise handling as the time interface. Merge sort's recursive,
merge and copy-back calls preserve their mathematical slice expressions in
continuations instead of expanding them merely to match argument bindings.
This reuses restored-call rules; it is not a new stage semantics.

`TimeExact` supplies exact-count composition over the existing measured
execution. Factorial's upper bound and measured endpoint reuse its one cost
induction. `ram_run_eq` and `ram_run_bound` account for real outer-call overhead.
Search's logarithmic proof reuses `while_div` and a budget-free halving relation.

Uniformly bounded continuations compose with `TimeBound.seq_const` without a
functional or termination premise. Map's separate time proof now composes call,
straight-line and traversal bounds without destructing measured executions.
This does not supply the intermediate behavioral facts needed for a bound that
depends on changed data.

**Next work:**

- Reduce repeated source-stage composition in recursive correctness and time
  proofs. Merge sort's typed calls already avoid raw call ASTs and restoration
  equations; its remaining split/reassembly mathematics should not be mistaken
  for missing calling-convention automation. Target actual repeated bookkeeping,
  retaining the recurrence, nonrecursive toll and changed-data facts.
- Extend exact composition to value/state-dependent continuations when an
  existing exact-count client needs it. Do not add an unused exact wrapper to a
  client already served by an upper bound.
- Mutable input-dependent traversal costs must follow actual elements, state and
  order. The current map uses a uniform helper bound; read-only fold's varying
  cost rule does not establish arbitrary mutable helper effects.

Correctness and termination stay budget-free. A conditional cost theorem alone
does not establish that an execution exists, nor is it automatically monotone
in allowed call depth. Time may use separately proved behavioral facts, but
behavioral equality between algorithms cannot transfer their runtime costs.
Natural subtraction alone cannot justify an overspent reserve.

**Acceptance evidence:** calls, assignments, loops and recursion decompose the
same declared computation in both proof views. A real varying-work continuation
gets its needed value and representation without unpacking measured execution.
The mathematical reserve/recurrence and actual capacity conditions remain visible.

## Priority 3: finish compositional data and runtime observations

**Available foundation:** typed contracts, `Part` observations and executable
`apply`/`applyState` are views of one declaration. Typed projection rules derive
ordinary value properties without per-client field decoding.
Copy returns complete represented arrays to its continuation; its reference view
still uses the original three runtime words, with destination length justified
by input representation, not inferred through encoder injectivity.

Shared two-buffer slice/reassembly rules carry unchanged halves across recursive
calls. Merge sort's `Stages` uses them independently of register and return-field
layout. Mathematical list and graph properties remain upstream mathematics.

**Next work:**

- Improve repeated multi-buffer composition at actual call boundaries. Transport
  lookup, bindings and routine frames; leave genuine containment, aliasing,
  representation length and mutation obligations explicit.
- Derive reusable declaration-level admissibility/observation conveniences where
  consumers still repeat them. Do not create a third function container, a new
  runner, or a wrapper around an already short equation.
- Prefer returned-value/shared-state contracts to reconstructing values from
  destination registers. A terminal time call with no continuation need not be
  migrated to a richer result interface merely for uniformity.

**Acceptance evidence:** the implementation-side proofs for slice, copy-then-sum
and recursive sort compose named operands and represented data. Their published
mathematical statements and separate cost bounds concern the actual compiled
invocation without per-client raw-code declarations or extracted result slots.
Scratch mutation is retained even when a contents-level specification omits it.

## CALF and related work: obligations, not labels

[CALF](https://arxiv.org/abs/2107.04663) guides the distinction between values and
computations, behavioral equality and cost-sensitive reasoning.
[Refinement with Time](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.20)
guides compositional representation transport.
[Decalf](https://arxiv.org/html/2307.05938v4) warns against discarding effects when
comparing costs. Their computational models do not establish our RAM bounds.

For this library the concrete obligations are:

- Results, effects and costs observe the same executable declaration.
- The source cannot inspect proof budgets or its measured transition count.
  Erasure and determinism connect measured and unmeasured executions.
- Correctness/termination do not depend on a proposed bound. Behavioral equality
  supports mathematical reuse, not automatic transport of algorithmic cost.
- Calls pass actual intermediate values and changed representations in execution
  order. Pure list identities do not justify reordering effectful helper calls.
- Primitive and calling costs follow from emitted instructions, not accepted
  annotations, unchecked ticks or free host computations.

This is not a port of CALF's modal type theory, Decalf's effectful language or
Sepref's synthesis. Read a small relevant part of a primary paper when a sample
exposes a design question; record the applicable distinction and its limits in
the literature notes, then return to the implementation.

## Later work and limits

The cost model is word-RAM transitions, not Lean wall time, comparison count or
bit complexity. Whole-problem claims fix the encoding, input domain, width policy
and size measure and quantify one program over legal inputs.

Borrowed descriptors, mathematical views, allocated storage and data conversion
are distinct. General allocation/loaders need actual implementations and costs;
preloaded-memory contracts do not claim them.

Space needs observations of live resources on the same execution. Address-space
capacity is not peak live storage. Establish stack liveness before stack-space
claims, allocation/reclamation before general live-heap claims.
Cross-model complexity requires a costed simulation and justified encoding.
Do not let more machine models, class catalogs or recurrence wrappers displace
the proof-experience priorities above.

## Working discipline

Use real consumers to identify the next obstacle, reuse or improve a shared rule,
check affected modules on the designated server, and update the evidence here.
Keep in-progress work distinct from verified interfaces. Reassess the plan when
a sample exposes a missing premise, unaccounted operation or unusable abstraction;
existing code is not a reason to preserve a poor interface.

Use Lean's checks and the actual samples. No separate audit framework, checksum
machinery or unrelated test scaffolding is needed.
