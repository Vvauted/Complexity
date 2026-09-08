# Roadmap

Write one executable program, state its correctness with ordinary Lean mathematics,
and derive its complexity without reopening the machine implementation.
A pleasant DSL, reusable proofs and proof automation are parts of the same goal.

This roadmap is driven by the existing samples, not by the number of interfaces
or lemmas in the repository. [Design](DESIGN.md) records semantic boundaries;
[literature notes](LITERATURE.md) record what we take from other work.

## What the samples actually establish

The verified scalar-function baseline already supports independent functions,
budget-free correctness, separate compiled costs, and ordinary executable value
equations. The returned-array and genuine `Unit` migration is in progress:
checked backend modules or accepted syntax alone do not establish end-to-end use.

| Consumer | What works | What still costs the proof author too much |
| --- | --- | --- |
| [Factorial](../Examples/Ram/Factorial.lean), [FunctionRun](../Examples/Ram/FunctionRun.lean) | Ordinary induction proves the recursive function; its executable value rewrites to mathlib factorial under the stated word/stack conditions. | Separate time and exact-count proofs reconstruct body states, recursive calls and register updates. |
| [LocalBindings](../Examples/Ram/LocalBindings.lean), [ArrayFold](../Examples/Ram/ArrayFold.lean) | Calls reuse helper correctness; a shared traversal proves the list fold without exposing its cursor. | Exact helper costs still require measured-execution case analysis; the traversal cost interface expects a constant helper-body count. |
| [ArraySlice](../Examples/Ram/ArraySlice.lean), [ArraySliceProperties](../Examples/Ram/ArraySliceProperties.lean) | The implementation uses a borrowed slice; subsequent properties use ordinary `List.drop`, `take`, and sum identities. | The slice is currently a local descriptor, not the result of a reusable slice function; runtime publication repeats safety and call-overhead bridges. |
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
standard induction, asymptotic relations, and mathlib's Akra–Bazzi machinery.
Do not build replacements for these.

A confirmed small improvement is the word-sum algebra:
[Array/Sum](../Complexity/Computability/Ram/Array/Sum.lean) can reuse
`List.sum_eq_foldl`, `List.foldl_assoc`, and BitVec's existing associative addition
and zero identity. Keep the necessary encoding/modular-arithmetic bridge, rather
than maintaining a second collection of list-sum proofs.

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

## Priority 1: finish one typed function path

Complete the current multi-field migration across source semantics, both
compilers, checked arities, executable calls, DSL signatures, imported signatures,
typed observations and contracts. Word, borrowed array and `Unit` results must
use actual returned fields from the same callee execution.

Then make typed arguments and results available in the correctness interface,
not only in generated `eval`/`apply` entry points. Proof authors should not
unpack a raw list of return words or prove return-field lengths themselves.
A thin typed view must remain tied to the one declared implementation.

**Evidence of completion:** adapt the existing slice consumer so a function
returns a borrowed slice which another function passes to imported sum. Adapt
copy to genuinely return `Unit`, preserving its heap effects in copy-then-sum.
Their mathematical contracts and independent compiled costs must compose without
a stream driver, fabricated result fields, or host-side sequencing masquerading
as one compiled program. Recheck scalar and recursive consumers too.

A `Unit` value alone is not an observation of mutation or execution steps.
Use the same invocation's state/count interface to observe those effects;
a source-language `Unit` call still executes its body and calling convention.

## Priority 2: share source-facing correctness and cost decomposition

Build on the existing total-correctness and measured-execution rules.

- Provide declaration-driven call and sequence rules for both exact costs and
  upper bounds. Infer static bindings and real call overhead from the source.
  A cost equation remains something proved about the implementation.
- Give recursive functions reusable body/recurrence rules so factorial's cost
  proof uses its mathematical recursive argument instead of another register-level
  induction. Retain any stronger body invariant actually required; do not infer
  it from restored caller state alone.
- Extend the existing traversal interface to consume a callee's conditional
  `FunctionTimeBound`, first for a uniform per-step bound, then for bounds on
  the actual element and prefix accumulator. Reuse finite sums and existing
  traversal/framing proofs.
- Expose state-dependent continuation bounds through the existing call rules.
  Automate local restoration and routine representation transport; mathematical
  facts about updated data remain explicit.
- Let the existing runtime bridge normalize outer call/return/halt costs as well
  as static compilation obligations. Do not repeat trampoline and `callSteps`
  proofs in every sample.

**Evidence of completion:** `LocalBindings`, factorial, `ArrayFold`, and
copy-then-sum use the common rules. Their algorithmic proofs retain only relevant
invariants, contracts and mathematical cost arguments; neither exact-count nor
upper-bound clients reconstruct ABI blocks or measured execution trees.
Adapt the existing call-based fold to reuse a helper whose actual cost varies
with its input, and validate that composition. Re-instantiating a constant-cost
helper does not establish the promised data-dependent experience.

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
