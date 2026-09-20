# Consumer evidence and acceptance

Existing consumers establish specific capabilities, not arbitrary combinations.
Use them to evaluate complete author proofs, including all connection work.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## What the current programs actually show

The source-to-RAM path handles
scalar arithmetic, mutable borrowed buffers, while loops, recursive calls and
imports. Correctness, realizability and counted execution compose across those
imports, including two effectful calls at their actual intermediate heap.
These results are retained; we do not need another execution model or backend.

**Checked capabilities:** effectful range `for`, nested product patterns,
independent named loop contracts, their shared resource rules, the mathematical
array-task interface and top-tree foundations are joined by pure finite-range
`for`, native iterative factorial and inferred uniform structural budgets.
Factorial and the direct, composed and imported compiled traversal consumers
exercise these additions; the library, Examples and manual pass together on 0v0.
Buffer-element `for` is implemented without a dedicated verified consumer;
nested ranges, early returns and self-recursive calls inside pure ranges do not
yet have separate consumer coverage. Dynamic top-tree operations remain open.

| Evidence | Working capability | Remaining author-facing problem |
| --- | --- | --- |
| [Factorial](../../Examples/Language/Factorial.lean), [Scalar](../../Examples/Language/Scalar.lean) and [Remainder](../../Examples/Language/Remainder.lean) | Generated native functions, including finite-range iteration; ordinary equality proofs, one native termination argument for self-recursion, automatic source correspondence and total-contract conversion | Pure general `while`, mutually recursive families and buffers remain unsupported; this is not a restriction on the effectful function table. Mathematical proofs and separate resource arguments remain author work. |
| [Traversal](../../Examples/Language/Traversal.lean) | Actual range `for`, native `Array.map` result and outside-buffer frame; independent guard/body contracts feed correctness and resource proofs; named-loop tactics select capture views, lexical frames and totality conversion, alongside inferred uniform budgets | Mathematical mutable-coordinate patterns remain in loop proof leaves. General potential and allocation-aware loop setup still use their public rules. |
| [Two-buffer composition](../../Examples/Language/TraversalComposition.lean) | Callee contracts and shared frame automation preserve both actual results, including disjoint slices of one object | The author still supplies the contracts and real separation facts. Arbitrary overlap, footprint inclusion and array identities are not inferred. |
| [Structured values](../../Examples/Language/OptionalBuffer.lean), [allocation](../../Examples/Language/Allocation.lean) and [scoped scratch](../../Examples/Language/ScopeCompiled.lean) | Native products/options across imports and actual RAM returns; initialized allocation, non-escaping reclamation and repeated-workspace bounds | General sums/recursive data, arbitrary lifetimes and persistent pure collection encapsulation remain missing. |
| [Compiled factorial](../../Examples/Language/FactorialCompiled.lean) and [traversal](../../Examples/Language/TraversalCompiled.lean) | Separate range, nesting and instruction-bound proofs reach the actual halted runner; both use the shared typed execution result, and traversal reuses its source loop contracts without manual capture/totality setup | Further operation resource interfaces and source-facing numerical bounds remain open; named-loop automation does not infer mathematical invariants or ranges. |
| [Imported compiled traversal](../../Examples/Language/ImportsTraversalCompiled.lean) | Existing behavior and resource contracts are reused without a new loop proof | Import transport is implemented. Its existence does not finish frame automation, total-function interfaces or data-dependent numerical bounds. |
| [Splay](../../Examples/Language/Splay/Sequence.lean) | One in-place recursive source, a shared mathematical contract and typed RAM results with amortized sequence costs | Mathematical tree descent and potential analysis remain author obligations. Complete container APIs and source-facing peak-space claims remain open. |

There are three different kinds of work: remove routine proof bookkeeping;
design a better function/data abstraction; add genuinely missing language and
runtime operations. More tactics address only the first kind.

The proof-experience target is concrete: authors supply mathematical invariants,
descent, representation/alias facts, numerical ranges and potentials. Shared rules
should supply lexical-environment transport, control plumbing, callee-contract
composition and publication of the same actual execution. A new short theorem
does not meet this target if an equally long private adapter is still required.

## Structured algorithms and top-tree boundary

The checked [top-tree foundation](../TOP_TREE.md) is mathematical work,
using mathlib's graphs, subgraphs, paths and finiteness. It supplies clusters,
legal joins, edge decompositions, reusable fold specifications and path-composition
lemmas. Legal local rotations preserve the root, exact leaf order and additive
summaries; their new intermediate cluster must satisfy its real boundary bound.
The unconditional height bound is linear; this supplies neither a maintained mutable
top tree nor logarithmic dynamic operations. Node representation, expose/link/cut,
balancing/amortization and source-to-RAM implementation are separate remaining
obligations. Keep this mathematics independent of RAM and use it to avoid
reproving decomposition facts, not to expand the current compiler work queue.

**Advance when:** those constructs let one declaration express the intended
algorithm, and mathematical contracts compose without per-algorithm register
adapters. Their actual operations, storage and costs must all be accounted for.

## Splay proof exercise — checked

Use one actual `source_program` splay implementation to challenge the shared
proof interfaces. The selected representation uses three borrowed arrays for keys and left
and right child IDs, with zero denoting an empty child. Its recursive two-level
descent must implement real zig, zig-zig and zig-zag steps, including unsuccessful
searches. Reuse mathlib's `Tree` as the mathematical view; do not maintain an
independent host splay implementation or assign it an unrelated cost model.

Completion requires all of the following, not merely a verified rotation:

- [x] Prove successful source termination, preservation of inorder keys and BST
  order, valid unique node IDs, and the accessed/last-visited node at the root.
  Preserve the key array, unrelated nodes and the actual surrounding heap.
- [x] Connect the same implementation to the existing RAM realization and
  compiler-derived costs. Include recursive calls, field reads/writes and
  branches; any rotation-count abstraction needs a proved instruction bound.
- [x] Prove the logarithmic access lemma with a real logarithmic tree potential,
  then a sequence bound retaining initial potential. From an arbitrary initial
  tree, do not claim an unconditional `O(m log n)` total bound or worst-case
  logarithmic time for one access. Word capacity and the preloaded-input boundary
  remain explicit in the RAM claim.
- [x] Shorten the actual author proof through shared rules, check it on 0v0 and
  keep the remaining mathematical obligations visible. Do not count moving an
  equally long per-example adapter behind a short theorem as an improvement.

The complete [source correctness proof](../../Examples/Language/Splay/Correctness.lean)
and its callable total contract now check on 0v0, including the shortened
recursive branches. The proof uses one induction on the mathematical input tree,
with no time or capacity premise. Shared `source_eval` simplification replaces
the old per-example operational branch wrappers; recursive calls stay opaque
until their actual execution equations are supplied.

The complete [instruction bound](../../Examples/Language/Splay/Cost.lean) and
[halted RAM invocation](../../Examples/Language/Splay/Compiled.lean) now check too.
Their fixed coefficient comes from the compiler and covers the actual recursive
calls, field operations, branches and outer call/return/halt overhead. Shared
finite-word realization handles the copy/compare/read/write/call fragment.
The represented-tree interface derives all three column-index bounds from its
successful reads; clients need not carry another copy of those access proofs.
The [consecutive-call theorem](../../Examples/Language/Splay/Sequence.lean) constructs
actual halted runner results, carries their complete physical memory and I/O
into the next call, and supplies the per-access costs internally. For `m`
accesses to an initial `n`-node tree, its total word-instruction bound is
`K * (m * (3 * log₂(n + 1) + 2) + n * log₂(n + 1))`, with a fixed
compiler-derived `K`. A stronger theorem retains both endpoint potentials.
Query supply, host scheduling and initial loading are outside the preloaded-call
boundary; this is not a separately compiled batch-query driver.
The library, Examples and manual build together on 0v0 with
`lake build Complexity Examples ComplexityDocs`; the final source-correctness,
single-run and sequence theorems use only Lean's standard axioms.

The initial implementation review identifies these focused interface tasks;
revise them against the actual splay proof rather than treating them as a new
general-purpose framework project:

- [x] **Subtree-local frames.** Shared cell-local frames now preserve cells
  outside a subtree's node footprint *inside the same buffers*. Tree replacement
  rules compose the real recursive update and parent relink; rotation rules lift
  the actual stores once. Disjoint slices of one object remain supported.
- [x] **Real, final-state-sensitive potential accounting.** The shared finite-sum
  telescoping theorem now supports ordered cancellative additive monoids,
  including `ℝ`, and the tree access lemma retains logarithmic endpoint potentials.
  The actual RAM invocation theorem supplies the rotation-to-instruction bound
  for the same result, and the sequence theorem constructs the real call history.
  Source correctness retains no time-budget premise.
- [x] **Read facts and dependent cost-family selection.** The cost pass keeps
  successful read equations, selects the actual callee before assigning a
  uniform bound and preserves the arithmetic presentation expected by existing
  consumers. These are shared elaboration fixes, not a new evaluator or pricing
  table. Ordinary compiler-generated index bounds should reuse `Fin.isLt`
  rather than search a large algorithm/ABI context again.
- [x] **Keep callee results and heap facts in cost automation.** Successful
  reads retain their equations, and named calls reuse the supplied source
  contract for the actual returned value and heap. An explicit `next` function
  exposes the existing dependent call rules through the same interface. Scalar
  uses the returned increment to select different numerical bounds; traversal
  transports the actual final heap and frame to its next call. The general rule
  permits heap-dependent numbers, but these consumers do not demonstrate an
  allocating algorithm with a heap-size-dependent remainder. Splay's rotation
  tail remains uniformly bounded without repeating its tree-correctness proof.
- [x] **Named recursive and cost contracts.** Generated ordinary-parameter
  contracts and argument transport remove the repeated `Env` projections.
  The cost pass matches supplied recursive/rotation contracts at the actual
  callee, replacing the hand-written finite table. Its introduction rule handles
  the function-body wrapper and ordinary parameters. Tree descent and the
  mathematical bound remain the author's obligations.
- [x] **Publish the same execution without ABI-shaped boilerplate.** The shared
  typed execution rule constructs the actual result once. Splay and factorial
  state their mathematical result and independent cost bound against it;
  consecutive splay calls resume its actual complete memory. Range and capacity
  conditions remain explicit named fields, not hidden assumptions.
- [x] **Separate sufficient call depth from time.** `FunctionDepthBound`
  reconstructs the same realized execution at a smaller nesting allowance.
  Sequential calls reuse capacity, and only entering a callee adds a frame.
  Splay's grandchild descent gives `tree.height / 2` internal levels, with one
  outer frame. The sequence uses the uniform `initialTree.numNodes / 2` bound.
  This gives a tighter sufficient stack capacity, not a standalone exact
  peak-access or reachable-live-space theorem.

The access lemma, BST invariant and genuine non-aliasing/descent arguments are
mathematical obligations, not defects to hide with automation. The standard
analysis follows [Sleator and Tarjan](https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf);
the [AFP development](https://isa-afp.org/entries/Amortized_Complexity.html)
provides a verified reference, not a dependency or a proof of our RAM costs.
