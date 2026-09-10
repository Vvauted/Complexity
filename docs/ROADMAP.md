# Roadmap

Write one high-level program, state its correctness with ordinary Lean/mathlib
values, and prove its complexity with ordinary mathematics. Shared compilation
proofs connect both claims to the same implementation. RAM is the backend, not
the algorithm author's proof language.

This roadmap distinguishes working foundations, unresolved design choices and
evidence needed to advance. The detailed current mechanisms remain in
[HIGH_LEVEL_LANGUAGE.md](HIGH_LEVEL_LANGUAGE.md) and [DESIGN.md](DESIGN.md).
A checked backend theorem does not by itself establish a usable high-level
interface. The milestones below are capabilities, not a serial queue that puts
memory design after all scalar automation.

The cross-prover [design research](DESIGN_RESEARCH.md) compares actual Isabelle,
Rocq, HOL4, F*, Agda and Lean implementations. Its recommendation is a shared
mathematical contract layer with complementary pure-equation and mutable-VCG
interfaces. No surveyed framework supplies all of this repository's guarantees
by import, and a native total function is not a prerequisite for every
effectful proof.

## What the current programs actually show

The review baseline is commit `89479f7`. The source-to-RAM path already handles
scalar arithmetic, mutable borrowed buffers, while loops, recursive calls and
imports. Correctness, realizability and counted execution compose across those
imports, including two effectful calls at their actual intermediate heap.
These results are retained; we do not need another execution model or backend.

| Evidence | Working capability | Remaining author-facing problem |
| --- | --- | --- |
| [Factorial](../Examples/Language/Factorial.lean), [Scalar](../Examples/Language/Scalar.lean) and [Remainder](../Examples/Language/Remainder.lean) | Generated native scalar functions; ordinary equality proofs, one native termination argument for self-recursion, automatic source correspondence and total-contract conversion | Pure `while`, mutually recursive families and buffers are not supported; mathematical proofs and separate resource arguments remain author work. |
| [Traversal](../Examples/Language/Traversal.lean) | Real read/helper/branch/write loop, native `Array.map` result and outside-buffer frame | Public guard/body/round proofs still manipulate `Control`, local tuples and nested triples. Named variables alone have not completed the loop interface. |
| [Two-buffer composition](../Examples/Language/TraversalComposition.lean) | Callee contracts preserve both actual results, including disjoint slices of one object | Routine contents/frame consequences are manually transferred between calls. This is an automation gap, not permission to assume all buffers are independent. |
| [Source types](../Complexity/Language/Basic.lean), [allocation](../Examples/Language/Allocation.lean) and [scoped scratch](../Examples/Language/ScopeCompiled.lean) | Named initialized allocation, non-escaping scoped reclamation, resource linking and actual repeated-workspace bounds | Products/sums/inductive data, arbitrary lifetimes and persistent pure collection encapsulation remain missing. |
| [Compiled factorial](../Examples/Language/FactorialCompiled.lean) and [traversal](../Examples/Language/TraversalCompiled.lean) | Separate range, nesting and instruction-bound proofs reach the actual halted runner | Authors still see compiler cost names, loop-view transport and large representation/ABI-shaped publication theorems. |
| [Imported compiled traversal](../Examples/Language/ImportsTraversalCompiled.lean) | Existing behavior and resource contracts are reused without a new loop proof | Import transport is implemented. Its existence does not finish frame automation, total-function interfaces or data-dependent numerical bounds. |

There are three different kinds of work: remove routine proof bookkeeping;
design a better function/data abstraction; add genuinely missing language and
runtime operations. More tactics address only the first kind.

## M0 — Decisions and questions to settle

### Boundaries to retain

- One user-written implementation. Automatically generated views and lowerings
  are allowed; a separately maintained host algorithm is not.
- Independent source meaning, with the existing typed core and verified RAM
  chain retained. The core can describe faults and divergence without making
  every public function expose those possibilities.
- Correctness and successful termination need no proposed time budget.
  Structural recursion or a mathematical well-founded argument is compatible
  with this requirement; recursion does not require a partial public interface.
- Reuse Lean, Std, mathlib and existing library mathematics. Keep dependency
  pins and the absence of CSLib. Specifications may use arbitrary mathematics;
  executable operations need actual implementations and correspondence proofs.
- Preserve source aliasing, arithmetic meaning, actual effects and legal input
  domains. Backend limitations must be stated or discharged, not hidden.
- Costs belong to the declared implementation and selected backend, not merely
  to an extensional Lean function. Equal results do not imply equal costs.

### The current core is not the final programming interface

The intended pure-program experience includes an ordinary total Lean function
and its usual mathematical equations. An effectful implementation should expose
mathematical data contracts, not require every caller to unpack the heap monad.
This is stronger than renaming `ExceptT Fault (StateT Heap Part)`.

Two complementary approaches share the same contract and compilation layer:

| Approach | What it can genuinely improve | What it does not establish |
| --- | --- | --- |
| Generate success/result contracts, induction rules and proof views over the existing core | Removes repeated environment, outcome and contract conversion; reuses current semantics and compiler immediately | A `Part.get` projection is normally still noncomputable. If obtaining it requires the old complete correctness proof, the difficult proof has only moved. |
| Generate a total Lean definition and corresponding core from one supported source declaration | Ordinary recursion equations and mathematical proofs can become the primary interface; Lean checks the supplied structural/well-founded recursion | Requires a shared correspondence construction, including recursion. It is not permission to compile arbitrary Lean terms or hand-maintain two function bodies. |

The second is checked for the scalar pure subset; the first is the primary proof
route for genuinely mutable operations, not merely a temporary workaround.
Their shared contracts carry mathematical results, actual intermediate contents,
frames and successful termination. Generate both views from one supported
declaration where applicable; do not require independently written pure and
mutable algorithms. An in-place implementation is not obtained from a persistent
one merely by identifying their results.

Before broadening that subset, retain how one supplied termination argument
feeds the generated definition and terminating core correspondence without
another author-written induction. This promises proof transport, not the absence
of internal compiler proof obligations. Pure equations and mutable invariants
must both compose with existing imports and backend proofs.

Purity also needs a real boundary. Not writing memory is insufficient: a
read-only function can return a value depending on its initial heap. Borrowed
in-place mutation remains effectful. Hiding it behind an `Array → Array` API
requires an explicit abstraction of the input contents and a proved isolation,
ownership transfer or copying policy. Any actual copying must be implemented
and charged. Do not select an empty heap and call this heap independence.

## M1 — Function definitions and proofs that feel like Lean

**Status:** `source_program (pure)` now generates native total scalar functions,
their checked action correspondence and total source contracts. Scalar,
Remainder and self-recursive Factorial pass on 0v0. The supported call graph is
self-recursion plus acyclic calls; pure `while`, mutual recursion and buffers
remain unsupported.

These declarations establish the first pure source-proof gate. Preserve their
single-body, single-termination-argument construction while improving the interface:

1. Retain the generated public function, its equations and checked
   connection to the existing core. Keep implementation identity for costs
   even when behavior is exposed as an ordinary Lean function.
2. Reuse Lean structural/well-founded recursion and the existing source
   [recursive contract rule](../Complexity/Language/Verification/Recursion.lean).
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
resource conditions remain; all 50 Examples and both aggregate library/Examples
builds pass. Native Lean execution and RAM instruction cost are distinct runtimes.

**Reconsider when:** the new API only shortens the final theorem while requiring
the old proof first, or the correspondence is a new hand-written adapter for
each function. A small alias or an additional `simp` lemma does not meet this gate.

## M2 — Mutable algorithms with mathematical data contracts

**Status:** shared objects, aliases, operation specifications and complete
traversal proofs exist; modular proof automation remains incomplete. Named loops
now expose `wellFounded_spec` for Lean relations on their mutable locals and heap;
the existing Nat `variant_spec` is retained as a measure specialization. The
scoped scratch consumer uses this general rule, and Traversal remains compatible.

The checked [source-frame rule](../Complexity/Language/Effects/Heap.lean) uses `NoCellWrites` for the
statement and every callee preserves an exact heap-object prefix and existing
contents through actual execution, including faults. It permits allocation
initialization but conservatively rejects explicit cell writes; the allocation
consumer's `retained_frame` now uses this rule.

Borrowed-buffer APIs remain useful for explicitly in-place algorithms. Their
specifications should expose ordinary contents, lengths, results and permitted
updates. Library rules retain the actual heap internally; clients must not
confuse an old contents observation with the state after a mutating call.

1. Give the existing traversal a generated loop-contract entry point over its
   source locals and mathematical invariant. Public rules should handle the
   lexical tuple, guard/body composition and impossible control exits when
   justified by that block. Keep the general effectful-guard semantics intact.
2. Compose supplied callee contracts and transport their proven frame
   consequences. Reuse `Buffer.Contents`, `Disjoint`, `PreservesOutside` and
   native `Std.Do` rules before adding new proof machinery. Contract content,
   real overlap conditions and algorithmic invariants remain author choices.
3. Share invariant and shape consequences with realizability and cost proofs.
   A different resource proof should not repeat the array-correctness argument
   merely to recover a length or unchanged region.
   Abstract callees may export a callable upper-bound function with an `IsBigO`
   theorem. Its useful monotonicity is a property of the selected bound, not an
   assumption that exact runtime must be monotone.
4. Provide captured-index traversal using existing range/iterator infrastructure
   after proving its correspondence. Each iteration reads current contents;
   a fixed-list snapshot is not the semantics of a mutable loop.

**Advance when:** the current Traversal and two-call/imported clients are proved
using a prefix invariant, Array mathematics, descent and actual frame facts,
without manual `Control`/local-tuple/WP-transformer transport. Two disjoint
slices of one object continue to work. Other overlapping views retain their
existing semantics. More concise proofs obtained by assuming no heap effects,
global no-aliasing or a special initial heap do not qualify.

## M3 — A language that can express structured algorithms

**Status:** first-order calls, while and self-recursion work. Richer values and
their associated programming/proof interfaces are missing.

Products and tagged results are the next data-language requirements: they allow
ordinary multi-result helpers and optional search outcomes without inventing
sentinel words. Their field/tag encodings must work through calls, returns,
imports, source proofs and resource transfer. A proof-local tuple used by a
loop is not an implemented product value.

Mutually recursive functions with different signatures and source
`break/continue` remain intended capabilities. Their proof interfaces and real
control-flow/cost connections must be supplied, not inferred from self-recursion
or ordinary function return; they are not prerequisites for the first M1 exercise.

Then add the pattern/recursion and collection interfaces justified by actual
algorithms, reusing upstream data types as mathematical views. Structural
recursion over a collection requires a real representation and operations;
adding a `List` type name does not provide them. Higher-order notation may use
proved static specialization before dynamic closures are considered.

Search should challenge the new proof interface with a different loop shape;
recursive sorting should challenge structured data, multiple buffers and
recursive composition. First reuse the old implementations' mathematical
lemmas through the connection layer. Do not create a catalog of new example
algorithms or claim old register-level examples are already high-level programs.

**Advance when:** those constructs let one declaration express the intended
algorithm, and mathematical contracts compose without per-algorithm register
adapters. Their actual operations, storage and costs must all be accounted for.

## M4 — Allocation, lifetime and encapsulated local mutation

**Status:** typed source allocation, its correctness/evaluator rules, general
measured simulation through loops and recursive calls, and the halted runner
connection are checked. Named `Buffer.alloc` and the complete allocating client
are checked too, as is allocating resource-import transport. The complete
library, all Examples, the routine source-frame consumer and the complete manual
build. Scoped scratch reclamation, its named mathematical contracts and the
same-source repeated-call runner/physical-workspace theorem are now checked.
Arbitrary lifetimes and encapsulated persistent pure results remain open.
Develop this alongside M1/M2; it constrains what a pure-looking collection API can mean.
See the [scoped reclamation checklist](RECLAMATION_TODO.md) for its concrete scope.

The first bottom-up layer is now implemented and individually checked:
[source heap allocation](../Complexity/Language/Heap/Allocation.lean),
[actual RAM allocation](../Complexity/Computability/Ram/Memory/Arena/Allocation.lean),
and the [typed runner connection](../Complexity/Computability/Ram/Compiler/Language/Arena/Execution.lean).
They prove initialization, old-object preservation, cursor persistence and
compiler-derived costs. The same allocator now has a five-slot inline instance,
including typed operand materialization, and checked call-boundary rules for
placement extension and explicit legacy metadata frames. `Stmt.alloc` now has
source semantics, `TotalWP`/VCG rules, source linking and static lowering.
The [general measured simulation](../Complexity/Computability/Ram/Compiler/Language/Arena/MeasuredSimulation.lean)
threads the same execution's final heap, extended placement and current
cursor through calls and loops; the [runner connection](../Complexity/Computability/Ram/Compiler/Language/Arena/ProgramExecution.lean)
includes private-flag initialization and the outer call/return/halt cost.
Independent source correctness can supply termination to the separate readiness
proof. Positive word width, exact values, rooted represented inputs and
code/stack/arena capacity remain explicit conditions; input loading and the
one-time bootstrap are separate. The [allocation consumer](../Examples/Language/Allocation.lean)
now exercises `make` returning fresh storage, a later caller allocation and a
real nonempty read (or empty return), with `retain_runUntil` preserving the
returned array's contents. `Named.make` has an ordinary `Array.replicate`
specification proved by `mvcgen`, with no source capacity or time premise.

The underlying `HeapRep` describes existing objects at one placement; the arena
simulation threads its extensions. `Buffer` is an object/offset/length view;
copying it or slicing does not allocate. `heapLimit` separates data from the
call stack. These borrowed-storage interfaces remain useful alongside allocation.

### Initial protocol and later lifetime extensions

- **Explicit caller-supplied output/scratch buffers:** retain as a useful
  low-level library interface. It does not satisfy construction of a fresh
  returned container and must not replace that requirement.
- **Stable-address monotone arena:** its typed source operation and general
  allocating execution to RAM, named construction and the allocating client
  and resource-import transport are implemented. The caller/session
  owns a still-live arena; nested calls share allocation progress, and returned
  containers remain there. Return does not reset the arena. Capacity accounts
  for retained input and cumulative fresh allocation across calls, not only one
  isolated callee when no explicit scratch scope is used.
- **Scoped scratch regions plus longer-lived results — checked:** `with_scratch`
  preserves writes to older objects and releases its fresh suffix after a
  non-escaping exit, including early return. Results allocated outside the scope
  remain live. Actual cursor capture/release costs six instructions and enables
  address reuse across calls and loops. This does not move/freeze results or
  establish a persistent pure collection API.

GC, reference counting and a new general ownership calculus are not selected.
Indirection/movable objects would require a real object table and additional
access costs; reconsider it if the desired sharing/resize API requires moving
objects. The choice must follow observable sharing and lifetime behavior.

Initially keep abstract source allocation separate from finite target capacity:
the source creates fresh initialized storage, and the target-success theorem
requires sufficient capacity. Do not claim a compiled out-of-memory exception
without implementing it. A future fallible API must specify ownership and
effects on failure. A pure facade over private mutation also needs representation
independence and persistent result semantics: a mutable buffer's contents
contract describes return-time contents, not an immutable value forever.

### Selected protocol and implementation obligations

The [concrete protocol](HIGH_LEVEL_LANGUAGE.md#selected-initial-allocation-protocol)
now selects a shared cursor at reserved RAM address zero, initialized once per
session. Allocation reserves a fresh interval, initializes it with actual stores,
then returns its descriptor. Calls retain the actual metadata and result storage;
the arena path is opt-in and does not reserve address zero in old RAM programs.
The runtime, representation and general simulation are checked. Their retained
boundaries and remaining integration/lifetime obligations are:

1. **Heap growth and representation — checked.** General execution preserves
   shape extension; allocation alone preserves exact old contents.
   The allocating simulation returns an extended placement and representation;
   subsequent calls encode their arguments and results with that actual
   placement. The fixed-placement no-allocation theorems remain unchanged.
2. **Live handles — checked.** The surface forbids constructing object IDs, but
   public `Buffer` inputs can still name nonexistent objects. A handle to a future ID
   could become valid after allocation while its old RAM encoding is stale.
   The simulation tracks rooted IDs in current and suspended caller values.
   Rootedness only requires an existing object slot, not a valid type/extent or no-aliasing.
   Placement extension preserves these descriptors. The new rooted-input
   condition is explicit and absent from the old no-allocation interface.
3. **Allocator state across calls and resource imports — checked.** The bump
   cursor is distinct from the fixed `heapLimit`. Actual shared cursor updates
   survive caller-local restoration, and compiled object accesses avoid the
   metadata. Raw legacy imports need a metadata frame or an allocating postcondition; `SafeExec`
   alone does not protect the cursor. Repeated entry must not rerun bootstrap.
4. **Initialization and capacity — checked, conditional.** Actual stores and
   address ranges establish initialized contents before observation; host-side
   `Array.replicate` is not free runtime allocation. Reserved and initialized
   prefixes are connected to counted execution, including zero-length overhead.
   Sufficient capacity remains a backend premise, not an implemented OOM result.
   Input loading and output conversion need an explicit boundary too.
5. **Escape and abstraction — scoped lifetime checked, encapsulation open.**
   A reset region cannot retain accessible aliases. `ScopeSafe` checks surviving
   locals and returns against the entry object domain; current cells contain
   scalars, not hidden pointers. Its source failure keeps the heap; compiled
   success requires a proved-safe exit rather than an escape scanner.
   Escaping aliases must not let later writes change a promised persistent pure
   result; prove the relevant isolation/freeze boundary or perform a real copy.
   Scope restriction retains exactly the current prefix of represented objects;
   outer results survive while repeated clients reuse scratch. Richer pointer
   cells or closures require extended root reasoning. Do not label the current
   physical workspace envelope as exact reachable live-space analysis.

**First allocation gate — checked:** a source callee allocates and returns a
container; its caller allocates again, uses the original and retains its
contents in the actual RAM result, including empty output. Behavior, capacity
and counted initialization compose without per-program register proofs.
This does not automatically infer mathematical ranges or loop/recursion
invariants.

**Scoped reclamation gate — checked:** one named declaration allocates a result,
repeatedly calls a worker with nested scratch arrays and returns the retained
result. Its source proof uses Lean's `measure` with no resource premise.
`Scope.make_runUntil` connects that same execution to actual halt, output contents
and all intermediate accesses within `entryCursor + 1 + 2*n + 2*frameSize`,
independent of repetition count. The bound includes retained heap, metadata,
scratch and two call frames; registers, code, I/O and host loading remain separate.
It is a sufficient physical workspace bound, not exact peak-live-space analysis.

## M5 — Source-level complexity and complete published claims

**Status:** compiler-derived step counts and independent conditional bounds
exist. Their public abstraction and problem-level composition are unfinished.

Keep three layers distinct: mathematical behavior; resource arguments over the
same source implementation; and a concrete backend adequacy theorem. Ordinary
function equality belongs to the first, not a way to recover the other two.
Further source-level resource inference is follow-up work here, not an open-ended
condition on the allocation foundation. Author-supplied mathematical ranges,
capacity and invariants are part of the proof, not missing compiler automation.

1. Expose proved operation/callee bounds at named functions and source arguments.
   Hide `lowerFunc`, function-table indices, register layout and ABI formulas
   in shared rules. Support actual result/state-dependent continuations using
   the existing general cost rules, not another interpreter or pricing table.
2. Generate the final typed execution theorem from behavior, realizability and
   resource contracts. Authors should not reconstruct the runner's large
   witness tuple, argument encoding or output decoding for each program.
   Remaining conditions must be meaningful source ranges and storage bounds.
   Preserve the algorithm's own precondition as well as representation and
   capacity assumptions. Domain-restricted total interfaces should use explicit
   domain arguments or an implemented error result, not an arbitrary default
   value extracted from a partial computation.
3. Reuse mathlib `IsBigO`, sums and recurrence results and the library's existing
   potential/composition tools. Derived asymptotic interfaces should hide exact
   implementation constants without hiding actual work or the admitted domain.
   Connect the existing [uniform time](../Complexity/Computability/Ram/Time/Basic.lean)
   and [problem certificates](../Complexity/Computability/Ram/Problem/Basic.lean)
   to the high-level declaration rather than creating another certificate system.
4. State the model early: current bounds count word-RAM instructions, including
   unit-cost word multiplication/division. They are not bit-operation bounds.
   Fix input encoding/size, legal inputs, width policy, one implementation family
   and the loading/output convention before publishing problem complexity.
   Current uniform certificates fix one emitted `Code` across inputs and widths;
   a more general width-dependent artifact family needs its own certificate bridge.
5. Distinguish stack/address capacity, occupied/reserved heap, cumulative
   allocation and peak live storage. Reuse existing
   [prefix/peak resource tools](../Complexity/Computability/Ram/Execution/Resource.lean),
   but provide an observation and lifetime connection for each new resource.
   A renamed capacity premise or cumulative access set is not live space.

**Advance when:** an algorithm author derives a mathematical complexity claim
and a typed execution guarantee for the same declaration without opening ABI
definitions. For an unbounded input family, the width/storage policy and cost
model must make the quantified statement meaningful. The current factorial's
linear word-step bound in numeric `n` is useful evidence, not a claim of linear
bit complexity or arbitrary-precision multiplication in constant time.

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

## Next work and when to change direction

Scoped reclamation and its same-source physical workspace guarantee are checked;
see [RECLAMATION_TODO.md](RECLAMATION_TODO.md). General lifetime inference and
encapsulation are not consequences of those theorems. The first bottom-up allocation queue is complete; see
[FOUNDATIONS_TODO.md](FOUNDATIONS_TODO.md) for its scope and checked builds.
Allocation, linking, scalar pure correspondence, Examples and the complete manual
now build together. The priorities below extend the supported fragments toward
the longer-term proof-experience goals.

1. Preserve the checked shared contracts and terminating correspondence for
   Factorial, Scalar and Remainder (M1), then address the unsupported pure
   constructs without duplicating the author's termination argument.
2. In parallel, exercise their mutable/VCG mode against Traversal and its
   two-call/imported clients (M2). Reuse the checked allocating client and
   arena/return protocol when improving the mathematical contract interface (M4);
   a pure scalar example cannot settle these abstraction questions.
3. Implement the shared interfaces justified by those exercises, then add the
   required structured values and container operations. Frame automation and
   dependent-call cost syntax are supporting tasks, not substitutes for them.
4. Keep M5's publication/model boundary in each consumer; do not defer the
   meaning of a cost or space claim until after its proof is written.

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
