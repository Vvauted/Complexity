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
| [Factorial](../Examples/Language/Factorial.lean), [Scalar](../Examples/Language/Scalar.lean) and [Remainder](../Examples/Language/Remainder.lean) | Generated native functions, including finite-range iteration; ordinary equality proofs, one native termination argument for self-recursion, automatic source correspondence and total-contract conversion | Pure general `while`, mutually recursive families and buffers remain unsupported; this is not a restriction on the effectful function table. Mathematical proofs and separate resource arguments remain author work. |
| [Traversal](../Examples/Language/Traversal.lean) | Actual range `for`, native `Array.map` result and outside-buffer frame; independent guard/body contracts feed correctness and resource proofs; named-loop tactics select capture views, lexical frames and totality conversion, alongside inferred uniform budgets | Mathematical mutable-coordinate patterns remain in loop proof leaves. General potential and allocation-aware loop setup still use their public rules. |
| [Two-buffer composition](../Examples/Language/TraversalComposition.lean) | Callee contracts and shared frame automation preserve both actual results, including disjoint slices of one object | The author still supplies the contracts and real separation facts. Arbitrary overlap, footprint inclusion and array identities are not inferred. |
| [Structured values](../Examples/Language/OptionalBuffer.lean), [allocation](../Examples/Language/Allocation.lean) and [scoped scratch](../Examples/Language/ScopeCompiled.lean) | Native products/options across imports and actual RAM returns; initialized allocation, non-escaping reclamation and repeated-workspace bounds | General sums/recursive data, arbitrary lifetimes and persistent pure collection encapsulation remain missing. |
| [Compiled factorial](../Examples/Language/FactorialCompiled.lean) and [traversal](../Examples/Language/TraversalCompiled.lean) | Separate range, nesting and instruction-bound proofs reach the actual halted runner; both use the shared typed execution result, and traversal reuses its source loop contracts without manual capture/totality setup | Further operation resource interfaces and source-facing numerical bounds remain open; named-loop automation does not infer mathematical invariants or ranges. |
| [Imported compiled traversal](../Examples/Language/ImportsTraversalCompiled.lean) | Existing behavior and resource contracts are reused without a new loop proof | Import transport is implemented. Its existence does not finish frame automation, total-function interfaces or data-dependent numerical bounds. |
| [Splay](../Examples/Language/Splay/Sequence.lean) | One in-place recursive source, a shared mathematical contract and typed RAM results with amortized sequence costs | Mathematical tree descent and potential analysis remain author obligations. Complete container APIs and source-facing peak-space claims remain open. |

There are three different kinds of work: remove routine proof bookkeeping;
design a better function/data abstraction; add genuinely missing language and
runtime operations. More tactics address only the first kind.

The proof-experience target is concrete: authors supply mathematical invariants,
descent, representation/alias facts, numerical ranges and potentials. Shared rules
should supply lexical-environment transport, control plumbing, callee-contract
composition and publication of the same actual execution. A new short theorem
does not meet this target if an equally long private adapter is still required.

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

The second is checked for the buffer-free scalar/product/option subset; the first is the primary proof
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
resource conditions remain; all Examples and both aggregate library/Examples
builds pass. Native Lean execution and RAM instruction cost are distinct runtimes.

**Reconsider when:** the new API only shortens the final theorem while requiring
the old proof first, or the correspondence is a new hand-written adapter for
each function. A small alias or an additional `simp` lemma does not meet this gate.

## M2 — Mutable algorithms with mathematical data contracts

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

The [named-loop resource tactics](../Complexity/Computability/Ram/Compiler/Language/LoopTactic.lean)
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

The checked [source-frame rule](../Complexity/Language/Effects/Heap.lean) uses `NoCellWrites` for the
statement and every callee preserves an exact heap-object prefix and existing
contents through actual execution, including faults. It permits allocation
initialization but conservatively rejects explicit cell writes; the allocation
consumer's `retained_frame` now uses this rule.

The shared [`buffer_frame`](../Complexity/Language/Heap/Tactic.lean) finishing
tactic composes already supplied `Buffer.PreservesOutside` and `Contents`
observations through their actual endpoint heaps. It reuses Aesop's logical
rules and the symmetry of known `Buffer.Disjoint` facts, without global Aesop
rule registration, array simplification or new alias assumptions. The two-call
correctness proof uses both supplied callee contracts through
[`source_vc`](../Complexity/Language/Verification/Tactic.lean): standard `mspec`
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

## M3 — A language that can express structured algorithms

### Language expansion scope

The following is the author-facing scope, not a list of names to make the parser
accept. Each capability needs the same source declaration, checked mathematical
meaning, actual executable operations and a connection to the existing RAM and
resource proofs. Representation lemmas alone do not complete a frontend feature.

| Capability | Required end state | Current boundary |
| --- | --- | --- |
| Ordinary containers | Contiguous `Array α` and `Vector α n`, and an actual linked-node `List α`, with composable behavior and cost contracts for their operations | Actual Nat-buffer copy/append and Array contracts are checked. Immutable nodes have shared-tail contents and complete RAM representation. Callable List emptiness, uncons, cons and a real callback-based fold reach the same halted RAM execution and full invocation bounds. Fold accepts an arbitrary represented accumulator and retains the original list through callback effects. Native List declarations generate mathematical functions, real fold/cons calls and checked correspondence, including allocated List results, List-valued fold accumulators and imported allocating callbacks. The remaining operation library, general element layouts and a complete persistent container frontend remain open. The Buffer List view is explicitly named `bufferList`. |
| User-defined data | Ordinary structures, `Sum`, recursive trees/lists, constructors, projections and useful pattern matching | Closed structures with direct scalar/scalar-product fields have checked registration, construction, projection, named calls and native mathematical proofs. Both the loop-free consumer and structure-valued finite ranges with helper calls reach the same halted RAM result and full instruction bound under explicit range/capacity conditions. General loops, structure recursion/matching, nested structures, general sums and recursive allocation remain open. |
| Polymorphism and refinements | Type parameters, registered algebraic operations, `Fin n`, dependent vectors and proof-bearing subtype parameters | Representation can erase subtype proofs while retaining their mathematical predicates. Static specialization, native telescopes and runtime uses of indices must be implemented; an erased index is not a free runtime value. |
| Higher-order programs | Function arguments/results, lambdas, closures and local functions | Statically known functions can be specialized first, but this does not complete escaping closures or higher-order return values. Their environments need real storage, root and cost rules. |
| Numeric types | Native `Int`, `UInt64`, `BitVec`, `ZMod` and their arithmetic, powers and bit operations | Scalar encodings/range facts and actual signed Int negation, comparison and addition are checked through halted RAM execution and compiler-derived costs. Those operations still have raw pair source signatures; native frontend selection and the remaining operators are open. |
| Control and effects | `break`, `continue`, explicit-step `for`, general matching, `try/catch` and ordinary I/O operations | Positive-stride ranges, including dynamic `k + 1`, have checked native correspondence. Exit-aware range rules also prove the actual guard/increment short circuits, but loop-exit syntax and arbitrary proof-bearing stride parameters remain open. Existing core faults are not catch handlers, and preloaded array invocation is not I/O. |
| Storage | Nested/pointer elements, resizing, arbitrary release and persistent pure results | Fresh Nat-buffer copy/append and allocating resize are checked, including prefix preservation and zero padding. Resize returns a new handle, not a moved object or in-place growth. Arbitrary release and pointer-bearing cells require live-root and alias protocols; return-time contents do not establish permanent immutability. |

The immediate dependency order is shared data representation and mathematical
contracts, real reusable container/scalar operations, and native type/operation
registration with automatically composed correspondence. Keep the existing raw
source observations while adding native typed observations from the same lowering;
do not replace them by a second hand-maintained algorithm. Control-flow work can
advance independently through the same existing backend. Closure and pointer
lifetimes must extend, not bypass, the current root/reclamation invariants.

The checked copy/append contracts also support native Array, List and
length-indexed Vector specifications through one source implementation.
`append_list_length` uses only ordinary `List.length_append` after the shared
refinement theorem. Fresh returned storage and every old contents observation
remain in that contract. These are mathematical views of contiguous Nat buffers,
not three runtime implementations or a complete native container frontend.
In particular, this Array-backed List view does not complete List support and
must not be selected as the default source List representation.

The shared allocating [`Buffer.Map.body`](../Complexity/Language/Buffer/Map.lean)
now has a checked `Array.map` correctness theorem. Each iteration performs an
actual read, calls the selected source function and writes its returned value;
the mathematical mapper occurs only in the supplied contract. The proof retains
fresh output storage and all old contents, and permits a callback to allocate
while preserving old contents. Its checked
[`Buffer.Map.program`](../Complexity/Language/Buffer/Map/Program.lean) adds an
actual callable entry through the existing program extension, preserving the
original callback and all of its calls. The checked
[`RAM connection`](../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Execution.lean)
publishes the same fresh result and retained old contents, with initialized
allocation, actual per-element calls and final return included in the bound.
Its numerical interface separates the sum of callback bounds from linear
traversal overhead; a constant callback bound gives a proved size-only affine
bound. The checked [asymptotic interface](../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Asymptotics.lean)
turns that same size-only budget into mathlib `IsBigO` in the input length,
without exposing its compiler coefficients to clients. This numerical theorem
does not discharge the actual invocation's word ranges or storage capacity.
The shared
[`scalar bridge`](../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Scalar.lean)
reuses existing nonallocating `FunctionRealizable` and `FunctionCostBound` proofs
without another callback resource proof. Arena growth counts retained output
and permitted callback allocation, not exact peak live space. Frontend
registration remains separate work: this is not yet native `xs.map f` syntax,
dynamic closures or a persistent pure Array interface.

### Concrete container implementations

The default runtime must match the selected data structure, not merely its
extensional mathematical contents:

- `Array α` and `Vector α n` use contiguous indexed storage. Vector's length
  proof is mathematical; persistence and copying still need an explicit policy.
- `List α` uses immutable nodes containing an element and a link to the next
  node. `cons` creates one node and shares its existing tail; `tail` returns the
  actual link without copying the suffix. Lists may share tails, so requiring
  global node disjointness is not an acceptable substitute for persistence.
- Linked-list `append` copies the left spine and shares the right list.
  Head/tail and cons should have constant structural cost for fixed-size element
  representations; length, indexed traversal and append have the costs of real
  link traversal. Element construction, allocation, callbacks and reclamation
  retain their separately justified costs. These are implementation obligations,
  not already proved complexity theorems.
- A List-valued specification of an array remains useful as an explicit
  mathematical view. It is not a reason to expose array copying or random access
  as the default implementation of List operations. Representation-changing
  conversions must execute and account for their actual work.

The List foundation uses typed immutable nodes, shared-tail contents and lifetime
rules connected to the existing heap and RAM representation. The source heap
operations and measured RAM allocation/nonempty-read blocks are checked. The
typed read and construction statements and their measured simulations are checked.
Construction uses the allocation-aware path; a read also supports fixed heaps.
Do not reinterpret Nat cells as arbitrary object pointers under the existing
direct-root-only scratch rule. Prefer the smallest sufficient immutable-node
protocol; this does not require choosing a general garbage collector first.

The first lifetime dependency is checked in
[`Heap.BackwardLinks`](../Complexity/Language/Heap/Backward.lean): when actual
object references point to earlier objects, retaining a root's heap prefix
preserves its entire reachable chain and those objects' current contents.
The concrete reference projection follows only node tails. Its preservation
rules and `NodeRef.Contents.take` retain a complete typed list when its root's
prefix is kept. This does not permit arbitrary Nat cells to act as pointers.

The source heap now distinguishes mutable scalar buffers from immutable nodes
with a Nat or Bool payload and a typed optional tail reference. Buffer lookup
rejects node objects; successful buffer writes preserve every node's actual
payload and tail. `Heap.cons` appends one node and shares its tail; `Heap.uncons`
performs the actual typed lookup. Their inductive `NodeRef.Contents` contract
exposes ordinary Lean lists and preserves old shared tails under buffer writes,
allocation and node allocation. The source operations and these preservation
proofs pass on 0v0.

Complete RAM heap representation now covers both object kinds. Nodes occupy
three words: the head, tail tag and tail's actual placement address, with zero
padding for `none`. Source identifiers need not fit a word. All-object separation,
backward links, placement transport, arena reservation and prefix reclamation
are checked together; buffer operations cannot overwrite represented nodes.
The [allocation bridge](../Complexity/Computability/Ram/Compiler/Language/Arena/NodeExecution.lean)
now connects one actual cursor update and three stores to the fresh node,
complete arena representation and `head :: values` contents. The
[read bridge](../Complexity/Computability/Ram/Compiler/Language/Heap/NodeExecution.lean)
connects three loads to the same head and shared tail while preserving the
entire heap. Their body costs, 21 and 13 instructions respectively, follow from
the existing compiler and describe those same executions. Operand preparation,
the empty-root branch, outer option packaging and call setup/return remain
outside those block counts. The typed read now reuses this same endpoint and
count in the general simulation. Typed construction additionally captures its
three operand fields, giving a proved 27-instruction block before the lexical
continuation. Complete callable operations retain their separate invocation
counts; a source definition is not a constant-cost RAM axiom.
The native proof facade must use the existing heap-indexed `Representation.Rel`:
different shared node layouts can denote the same ordinary List. The pure
structure frontend's lossless `Equiv` is not a global inverse for list handles.
Operation correspondence and immutable-content preservation must compose this
relation at actual intermediate heaps, without charging mathematical decoding
as an executable operation or assuming a mutable handle is persistent.

The first callable root operation is checked:
[`List.IsEmpty`](../Complexity/Language/List/Basic.lean) matches the actual
optional root, returns ordinary `List.isEmpty` and preserves the entire heap.
Its [compiler bridge](../Complexity/Computability/Ram/Compiler/Language/List/IsEmpty.lean)
connects that same source to a halted RAM result and a compiler-derived full
invocation bound. It needs no node read or traversal. The native frontend
registers `xs.isEmpty` and `List.isEmpty xs` in let-call bindings for the supported
Nat/Bool Lists. The existing `NativeViews.isEmpty` declaration inherits its
ordinary Boolean equation and reaches the same halted RAM invocation through
shared measured-call composition and inferred wrapper costs. Its reusable
readiness certificate needs no node lookup, head-element range or proposed time
bound; a complete RAM launch retains its actual representation and capacity
conditions. Heap and cursor are unchanged. Preloading inputs remains outside
the count; arbitrary expression-call hoisting is not implemented.
[`List.Uncons`](../Complexity/Language/List/Uncons.lean) now supplies the next
callable operation: it matches the root, reads a present node once, and returns
the head and identical shared tail. Its independent correctness theorem refines
ordinary `List.head?`/`List.tail` observations at the unchanged heap. The
[compiler bridge](../Complexity/Computability/Ram/Compiler/Language/List/Uncons.lean)
derives a constant full-invocation bound from the actual branch, read, option
packaging, return and call rules. The existing input List representation and
complete heap representation supply the lookup and word ranges; callers add no
register proof or tail traversal. Its composable `arenaMeasured` entry takes
ordinary list contents at the current heap and only the present head's word
range; it needs no physical heap representation or proposed time bound.
`arenaMeasured_of_heapRep` derives that range from an existing launch heap when
available. Both retain the actual read result, unchanged heap and cursor; the
separate cost certificate applies to the same execution. The existing `headOr`,
`replaceHead` and conditional inspection clients now compose these observations
directly, without unpacking Uncons execution/cost witnesses. The optional named
continuation mode pauses the shared call pass before a match, so `replaceHead`
prepares its returned-tail constructor certificate once for both branches.
Constructor counts and actual continuation heaps remain explicit. The native frontend registers `xs.uncons`
and `List.uncons xs` to this operation; its generated mathematical view uses
ordinary head/tail observations, not a new upstream Lean List definition.
The [named client](../Examples/Language/LinkedList.lean) writes the same operation
with `source_program`, optional-root matching and `ref.read`. Its generated body
is definitionally the public operation, so correctness and refinement reuse the
library theorems directly, without a per-client lowering adapter.

[`List.Cons`](../Complexity/Language/List/Cons.lean) supplies callable construction.
Its independent source contract gives `head :: values`, the exact fresh root
and allocated heap, and preservation of all previously represented lists.
The checked [compiler bridge](../Complexity/Computability/Ram/Compiler/Language/List/Cons.lean)
returns that same halted execution, the actual cursor increment of three words
and a full invocation bound including operand preparation, allocation, option
packaging and outer-call overhead. The named client writes `NodeRef.cons head tail`
and reuses the public contract by definitional equality. Its singleton also
infers the type of `none`; neither client supplies a register proof.
These root operations do not by themselves supply a native pure List API.

The shared [linked fold](../Complexity/Language/List/Fold/Basic.lean) now follows
actual tail pointers with a `while` loop and invokes the selected source callback.
Its source correctness and [callable entry](../Complexity/Language/List/Fold/Program.lean)
are checked on 0v0. The result refines ordinary `List.foldl` for an arbitrary
represented accumulator. The callback domain need hold only along the actual
mathematical accumulator trajectory. Callbacks may allocate or change mutable
buffers; old immutable-list observations survive by the shared heap-shape rule,
without an unchanged-heap assumption. Mathematical list induction supplies
termination without a time budget or recursive fold invocation.

The checked [fold RAM connection](../Complexity/Computability/Ram/Compiler/Language/List/Fold.lean)
retains those same callback returns and final memory, separates
accumulator-dependent callback bounds from linear traversal work, and includes
outer call/return/halt. The traversal itself needs no length-dependent call
depth. The initial reservation interface sums callback allowances; it does not
yet distinguish retained growth from reusable scratch peaks. The checked
[numerical interface](../Complexity/Computability/Ram/Compiler/Language/List/Fold/Asymptotics.lean)
expresses callback charges as an ordinary `List.mapIdx` sum over `take`/`foldl`
prefixes. Uniform callback bounds give a size-only affine envelope and mathlib
`IsBigO` in list length. A nonconstant bound only needs the common envelope at
actually visited prefixes. These numerical facts do not discharge word ranges,
capacity or callback correctness. Native fold syntax should select the same
implementation through heap-indexed refinement, not force shared list layouts
through the scalar frontend's lossless `Equiv`. Native construction and List
function results and List-valued native fold accumulators use the relational
facade below; general element layouts remain unfinished.

The checked [native callback bridge](../Complexity/Language/List/Fold/Native.lean)
accepts an allocating callback's actual evaluation and represented result through
`Contract.of_eval`; `eval_exists` retains the resulting accumulator, original
list and heap shape. Its pure specialization instead uses an injective
accumulator encoding and gives exact result and unchanged-heap equations from
the same generic fold contract. Neither route proves a second traversal or
requires a heap-independent encoding of lists. Existing callback
range and cost proofs similarly feed the fold through the shared
[finite-function bridge](../Complexity/Computability/Ram/Compiler/Language/Arena/FunctionResources/Finite.lean).
The fold itself now exports [callable resource contracts](../Complexity/Computability/Ram/Compiler/Language/List/Fold/Resources.lean),
so a containing program can reuse its body bound and allocation allowance.
Its `ready`, `functionResources_of_ready` and composable `arenaMeasured_of_ready`
interfaces need no callback time bound. The last retains the actual compiler
count without prescribing an upper bound. The shared readiness proof lifts the already proved finite source loop;
it no longer repeats the list induction to assemble a new traversal.
The native read-only `realizable_of_resources` entry also drops the callback
cost premise; the existing scalar sum consumer uses it, keeping instruction
analysis in its separate cost proof.
These interfaces retain initialization and actual intermediate heaps; a caller
must still compose its own calls and charge its own complete invocation.

The opt-in [represented frontend](../Complexity/Language/Syntax/Represented.lean)
now generates ordinary Lean functions and node-backed source functions from
one `source_program (native)` declaration. The checked
[linked-list consumer](../Examples/Language/LinkedList.lean) includes a constant
initial accumulator, reordered parameters, immutable locals, two consecutive
folds and calls to earlier functions in the same family. Its mathematical
proofs use ordinary List sum equations. Generated `_refines` proofs carry the
actual input representations internally, and `Refines.of_math` combines them
with the author's mathematical theorem. No disjointness is required between
immutable input lists, and shared tails are not copied. Native fold operations
use statically selected pure callbacks or allocating callbacks imported from a
completed native family, with scalar/product or List accumulators. Native
callback correspondence uses the existing general fold contract and actual
final-heap result relation. Native blocks compose immutable lets, registered
calls, final returns and explicitly typed conditional result bindings. Each branch
can allocate and return a supported represented value to a common continuation. The
`NativeBranches.choosePrepend` and `chooseSum` consumers have checked ordinary
equations and generated relational correspondence on 0v0. The compiler reuses
existing source branches and summarizes their actual result/heap relations before
proving the common continuation once. The `NativeViews` family additionally
checks recursive products/options containing Lists, their projections and
preservation across actual allocation. Its List matches lower through the
real Uncons call and existing Option match, with head/tail projection copies;
Option matches retain the actual stored payload. Both support exactly two
branches and an explicitly typed result binding over supported scalars, Lists,
and their recursive products/options. Ordinary equations and generated source
correctness are checked, including `replaceHead` followed by a constructor call.
`headOr` and `inspectOrPrepend` also have end-to-end RAM theorems for their scalar
and compound results; `headOption` remains at source correctness and generated
correspondence. Initialization and field copies remain actual source operations;
bare node and buffer result slots are
not admitted. General patterns, native recursion and escaping callbacks remain
separate frontend work. This does not restrict the
more general effectful fold library or change the existing `(pure)` path.

The same frontend also accepts `List.cons`, `head :: tail`, explicitly typed
empty lists and List-valued function results. The `NativeConstruction` consumer
allocates and returns a list, composes two list-returning calls, and folds both
the original input and its new extension after allocation. Ordinary List
equations specialize its generated `_refines` without a per-function heap proof.
The [constructor observation](../Complexity/Language/List/Cons/Native.lean)
reuses the real allocating entry's existing total contract. Generated
`_action_rel_native` proofs follow the actual returned roots and intermediate
heaps; `Representation.list_mono` retains every earlier List observation across
each call. Read-only scalar functions keep their existing exact unchanged-heap
equations. Allocating functions do not get such an equation, and no mathematical
List decoder or tail-validation traversal is introduced.

`NativeLists` additionally imports an allocating cons callback into a List-valued
fold. Its reverse/append, reverse, preceding cons and subsequent sum consumers
have checked ordinary mathematical equations and generated correspondence on
0v0. The reverse/append theorem reuses Lean's `List.foldl_flip_cons_eq_append'`;
the author supplies no source-heap induction. Imported native functions retain
their checked signatures and relational observations, so the same callback is
available for both a direct call and an actual fold. This extends the native
function boundary, not the node element layout or dynamic-closure semantics.

The [native allocating consumer](../Examples/Language/LinkedListAllocation.lean)
connects both `NativeConstruction.prepend` and `prependPair` themselves to the
halted RAM runner.
The shared [constructor-call bridge](../Complexity/Computability/Ram/Compiler/Language/List/Cons/Call.lean)
reuses the imported constructor's measured execution and the existing call/return
rules. The wrapper's exact instruction count includes both call levels,
initialization, its own return and final halt. The same result retains the fresh
root, actual final heap, shared old tail and cursor advance of three words,
independent of tail length. Input loading remains outside the bound; word,
code/stack and arena capacity remain explicit. The two-call consumer invokes the
actual `prepend` body twice, retains the first call's heap and cursor, and proves
an exact six-word cursor increase and complete invocation count. Sequential
calls reuse the caller depth rather than summing their nesting allowances.
The shared [allocating-call composition](../Complexity/Computability/Ram/Compiler/Language/Arena/FunctionResources/Call.lean)
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

The [allocating-fold consumer](../Examples/Language/LinkedListFoldAllocation.lean)
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
The checked [structural arena proof pass](../Complexity/Computability/Ram/Compiler/Language/Arena/Tactic.lean)
now reads the actual call/let/return statements and composes their existing
execution, readiness and cost rules. Both allocating consumers, including their
`prepend` and `push` constructor wrappers, no longer construct `Args`/`EnvFits`,
relocate callee proofs or build operational return continuations by hand.
Exact calls consume a measured callee; contract calls consume independent source
totality, resources and a bound. Imported function identity is recovered from
the actual call and its supplied table embedding, without opening callee bodies.
The generic contract form keeps mathematical resource indices explicit: they
cannot be reconstructed from raw list handles. The shared
[`List.Fold.arenaMeasured_of_ready`](../Complexity/Computability/Ram/Compiler/Language/List/Fold/Measured.lean)
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

The [indexed arena call rules](../Complexity/Computability/Ram/Compiler/Language/Arena/CostBound/Call.lean)
select an existing callee bound at a mathematical input index, checking its actual
arguments and entry-heap precondition. The structural cost pass accepts
`certificate at index via embedding`; it does not infer a List from its root or
guess an input-dependent price. Adding `using specification` reuses an existing
`FunctionTotal` postcondition at the actual returned value and heap. This lets a
later call use the represented result as its mathematical cost index, rather than
bound impossible outcomes. The general `_le` rules additionally accept a
result-dependent continuation budget and a proved combining inequality; that
mathematical inequality is not inferred by the structural pass. The shared
[allocating-loop rule](../Complexity/Computability/Ram/Compiler/Language/Arena/CostBound/Loop.lean)
uses an author-supplied ghost index, invariant and potential over the actual states.
It includes false exits and early returns, retaining the actual changing heaps
and cursor endpoints. It bounds an already given execution, not its termination.

The [indexed readiness rule](../Complexity/Computability/Ram/Compiler/Language/Arena/Loop.lean)
likewise follows an existing successful finite source loop, but requires no time
potential. Its invariant carries a mathematical index and the actual arena
cursor. Actual guard and body endpoints are connected internally; normal rounds
choose a next index, and early returns retain their own postcondition. It does
not restrict allocating rounds to a fixed cursor. The
[fold readiness proof](../Complexity/Computability/Ram/Compiler/Language/List/Fold/Ready.lean)
uses the existing source `loop_total`, callback resources and accumulated
reservation to instantiate this rule, retaining ranges and shared-tail
observations at the actual new heap. No second list/termination induction or
callback time bound is required. This is a reusable proof rule, not automatic
invariant discovery or a peak-live-space result.

The [fold cost proof](../Complexity/Computability/Ram/Compiler/Language/List/Fold/CostBound.lean)
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

The [allocation-then-traversal consumer](../Examples/Language/LinkedListComposition.lean)
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

The [typed-join RAM consumer](../Examples/Language/LinkedListViewsCompiled.lean)
uses the same inferred bounds and publication rule. `headOr_execute_le` returns
`values.head?.getD fallback` and preserves the entire heap and cursor.
`inspectOrPrepend_execute_le` returns its represented optional head/tail and List
together, retains the original List, and advances the cursor by three words only
on the true branch, with no growth on the false branch. Both bound the complete
preloaded invocation, including actual result-slot initialization and field copies.
Their uniform instruction bounds do not assert an exact branch-dependent count
or remove the real launch and selected-path capacity conditions.

The [compiled native consumer](../Examples/Language/LinkedListCompiled.lean)
now reaches the actual `Native.sumFrom` wrapper's halted RAM result, not merely
the separately runnable fold operation. A bound on `initial + values.sum`
supplies every intermediate addition range. Shared read-only bridges reuse
the existing call-realizability and cost tactics; the resulting bound retains
the wrapper's own call, return, initialization and outer halt. Source correctness
and exact heap preservation still have no word-range or time-budget premise.
The [ordinary-parameter resource interface](../Complexity/Computability/Ram/Compiler/Language/List/Fold/Native.lean)
now constructs the fold's environment and representation index and supplies
the zero-growth arena-to-fixed conversion. The consumer provides mathematical
prefix admissibility, ranges and existing callback resource facts; it no longer
repeats that generic environment/arena transport. This is not automatic resource
inference for arbitrary native declarations. The additional `sumPair`, `sumTwice`
and `sumWithPrepended` consumers have checked correspondence, but not yet their
own published RAM bounds. The allocating `reverseAppend` wrapper is covered
above, and `reverseSum` has the complete invocation bound just described;
`reverseWithHead` does not yet have its own published RAM theorem.

The allocation bridge now has `cons_of_rooted` and `cons_measured_of_rooted`:
the raw node operation only needs an existing tail root, while its List
specialization adds the complete mathematical contents. Both versions reuse
the same actual allocation; neither performs a tail validation scan.

The typed core now has `Ty.node`, with an optional reference as the list root.
Existing option construction and matching handle the empty case. Its value
encoding, rootedness, placement transport and effectful parameter/return syntax
pass together on 0v0. A reference is encoded by its actual placement, never by
truncating its source object ID, and is not accepted as a numeric scalar or a
heap-free pure parameter. `Representation.list` uses the actual linked contents;
the array-backed observation is separately named `Representation.bufferList`.

`Stmt.readNode` binds the actual head and optional tail, with success and fault
semantics, source proof/observation rules, linking and measured simulation on
both fixed heaps and allocating continuations. The effectful frontend accepts
`let (head, tail) ← ref.read`; this is a heap statement, not a pure `Prim` or a
host callback. A missing or wrongly typed object faults without mutating the heap.
`Stmt.consNode` similarly binds the fresh reference from the actual allocator;
the effectful syntax is `let ref ← NodeRef.cons head tail`. Its continuation can
allocate again at the updated cursor. Existing-object rootedness alone
does not guarantee that a node's tail is rooted: `Exec.rooted_backward` explicitly
preserves rooted values and backward links together, using the initial invariant
already supplied by the complete arena representation.
The first element layouts are Nat and Bool; general `List α` requires a separate
extension of node payloads. Native list equations must compose heap-indexed
contents refinement, rather than reuse the structure frontend's lossless `Equiv`.
Native cons allocation and List-valued results use the same typed core through
the relational facade above. The remaining traversal operations and general
element layouts remain open.

The shared action layer is checked in
[`Eval.Node`](../Complexity/Language/Eval/Node/Basic.lean) and its
[`Verification`](../Complexity/Language/Eval/Node/Verification.lean) rules.
`NodeRef.consM` and `readM` use the same heap operations and existing
exception/state monad. Default `@[spec]` rules carry raw operation facts;
separate List rules carry ordinary cons contents, actual shared tails and old
list preservation. The read statement's generated observation now reuses
`readM` and these same specifications. The construction statement's observation
likewise uses `consM`; neither rule adds a tail check.

Keep the two operation boundaries explicit. A nonempty-node read binds the
actual head and optional tail from one typed lookup; a missing or wrongly typed
object faults in the unchanged heap. Node construction binds one fresh reference
from `Heap.cons`; it neither traverses nor checks the tail. Existing option
matching supplies the empty case. Successful mathematical List contracts supply
the stronger finite typed-chain observation independently of these raw actions.

The source safety proof must preserve rooted locals, rooted results and backward
links together. Reading a tail uses the initial backward-link invariant;
constructing a node preserves it because the operand's root belongs to the old
domain. Existing arena simulations already carry that invariant in `HeapRep`.
This changes the source preservation theorem's hypotheses, not the operations
or the public arena launch conditions. Scope cleanup keeps the current prefix,
and no runtime reachability scan or rollback is introduced. Ordinary fixed-heap
simulation can handle reads; allocation belongs to the existing arena path.

The current scalar `Refines.of_encoded_eq_pure` rule requires an unchanged heap;
it is not the correspondence rule for an allocating List function. The native
frontend instead uses `FunctionRepresentation.ofResult` and
`RepresentedFunction.Refines` to relate List results to actual final-heap
contents, while carrying preservation of existing immutable lists across calls.
The mathematical function remains pure even though its implementation allocates;
this does not erase that allocation from RAM execution, capacity or cost proofs.

**Status:** first-order calls, while, recursion and the first structured-value
layer are implemented. Native Lean `Prod` and `Option` values now pass through
constructors, projections, assignment, real matching, calls, returns and imports.
Their source contracts, word ranges, actual lowering and instruction counts use
the same execution. The frontend supports nested product patterns
and `_` in immutable bindings, including `let (x, y) ← call` and `some (x, y)`
branches. The right-hand side runs once; projections and copies are real generated
operations. This does not implement general algebraic patterns, sums or recursive
data representations. The revised structured consumer's source and actual RAM
theorems are checked together with the whole library.

The new native-structure path is separately checked in
[`Scalar`](../Examples/Language/Scalar.lean) and
[`ScalarCompiled`](../Examples/Language/ScalarCompiled.lean). A registered
ordinary structure is constructed, passed to a source callee, returned and
projected; that callee imports the existing scalar helper. Its mathematical
proof only reuses the helper's ordinary minimum equation. Generated native/core
correspondence and total contracts feed the existing range and cost automation,
and the final theorem describes the same halted RAM result. Reconstruction of
raw scalar layouts is generated and checked once at the connection boundary,
not written by the algorithm author or installed as an uncharged operation.
This does not extend reconstruction to arbitrary partial representations such
as bounded subtypes. The native-structure pass remains pure and nonrecursive,
with only direct scalar or scalar-product fields.

`StructuredRange.sum` additionally keeps a native structure as a mutable
accumulator across actual helper calls inside a finite range, including dynamic
positive stride and a helper call before entry. Its ordinary fold/sum theorem
and generated total source contract are checked on 0v0. The connection layer
transports native and raw loop coordinates through checked equivalences;
algorithm authors do not supply encode/decode lemmas or a second loop proof.
Its generated native guard/body equations now take one captures tuple, with
endpoint/stride selectors derived from the actual range metadata. The shared
[`while_range_encoded`](../Complexity/Computability/Ram/Compiler/Language/CostBound/Range.lean)
rule supplies round-count descent and normal/early-return accounting using
the existing compiler costs and `Std.Legacy.Range.size`. The complete function
body has an inferred bound in its ordinary start/stop/step parameters, independent
of the initial structure and heap. `structuredRangeSumBodyBound_eq` exposes it
as a fixed per-round charge times the ordinary range length plus fixed overhead;
both constants follow from the same compiler proof. Its consumer no longer builds private block
contracts or guesses captured-variable positions. The checked shared
[`RealizationWP.while_range_encoded_invariant`](../Complexity/Computability/Ram/Compiler/Language/Realization/Range.lean)
also supplies finite-range termination while retaining the author's mathematical
invariant at normal exit. The dedicated `structured_range_sum_execute_le`
connects the same ordinary result and budget to an actual halted invocation,
including outer call/return/halt. Its extra word conditions cover the final sum,
last actual cursor and computed stride, even for empty ranges; the launch retains
input, code and stack conditions. The shared
[`ram_source_locals`](../Complexity/Computability/Ram/Compiler/Language/LocalsTactic.lean)
pass selects the loop's registered view, endpoint and structure-encoding equations
from its namespace. Standard tactic locations restrict which hypotheses or target
are normalized; callee bodies, mathematical invariants and cost functions stay
closed. This removes repeated coordinate lemma lists in the structured range
and mutable traversal consumers. The traversal's named-loop resource tactics
also select capture views and fixed-capture frames from its existing contracts.
The structured range uses its separate encoded-range rules. Further resource
composition remains open; it must not add another per-program termination or
register proof.

The existing multi-field ABI concatenates product fields and places an option
tag before its fixed payload. `none` has canonical zero padding, not a default
buffer; only the selected `some` branch receives a payload. Copying and matching
have actual emitted costs. Recursive rootedness preserves the existing aliasing
and scratch-escape conditions even when borrowed views are nested in a tuple or
option. Mutable buffer cells remain scalar; this adds neither a new allocator nor a
global inverse of the buffer encoding.

The [complete consumer](../Examples/Language/OptionalBufferCompiled.lean) imports
a pure helper returning `Option (Nat × Nat)`, constructs a full borrowed slice,
and returns `Nat × Option (Buffer Nat)` through another imported call. Its client
matches that actual result, reads and increments the first cell only when present,
and returns the structure. Ordinary array contents and frame contracts connect to
the real RAM result, four return words and a compiler-derived instruction bound.
The public execution theorem states the mathematical postcondition and time bound;
physical encoding consequences are separate projections of that same result.

Effectful functions already share a typed table supporting different signatures
and mutual calls; the pure native-function frontend has the narrower restriction
described in M1. Explicit positive range steps now share the native range
correspondence, including a dynamic `k + 1` consumer. The bounds and stride are
frozen once. The current generated proof must establish positivity from the
expression; a general user-supplied proof parameter is not yet accepted. The
RAM range condition includes the last increment actually executed, which may
exceed the stop value. Pure general `while` and source `break/continue` remain
open. Their semantics and proof/cost interfaces must be supplied, not inferred
from existing effectful loops or ordinary function return.

Then add the pattern/recursion and collection interfaces justified by actual
algorithms, reusing upstream data types as mathematical views. Structural
recursion over a collection requires a real representation and operations;
adding a `List` type name does not provide them. Higher-order notation may use
proved static specialization before dynamic closures are considered.

Use existing consumers to select the next missing operation or representation.
Reuse old implementations' mathematical lemmas through the connection layer;
do not create an algorithm catalog or call old register-level examples
high-level programs merely because their theorem names are accessible.

The checked [top-tree foundation](TOP_TREE.md) is mathematical work,
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
   locals and returns against the entry object domain; mutable buffer cells
   contain scalars. Immutable nodes have explicit backward links, and the
   all-object representation preserves their chains under prefix restriction.
   Node references use entry-domain rootedness as language values.
   `Exec.rooted_backward` preserves rooted values and backward links together,
   including a read's exposed tail. The construction statement preserves this
   invariant by sharing a tail rooted in the existing object domain.
   Source failure keeps the heap; compiled
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
exist. The shared `FunctionCapacity`/`FunctionLaunch` and `FunctionExecution`
interfaces now separate admissible preloaded inputs from the actual typed
runner result. Factorial and splay use the same `execute_le` rule; neither
reconstructs the old runner witness tuple. Named calls accept an explicit
result/heap-dependent continuation bound; the scalar consumer checks a
returned-value-sensitive bound, and traversal checks actual heap/frame transport.
`FunctionArenaLaunch` and `FunctionArenaExecution` provide the corresponding
allocation-aware result: actual final placement/cursor and complete machine memory,
with the known call depth retained. The scoped-workspace consumer now uses this
shared result and its actual access-set bounds instead of assembling a large
runner tuple. Concise loop-resource interfaces, further consumer migration,
general live-space observations and problem-level composition remain unfinished.

Uniform structural budgets are inferred through the existing checked cost rules.
Traversal's guard/body witnesses are chosen before arbitrary locals and heaps,
and its function wrapper is inferred around the supplied loop bound. Direct,
two-call and imported clients reuse the named bounds instead of copied constants.
`whileLinearBound` supplies structural loop charges; the author still supplies
the iteration measure, potential inequalities and any data-dependent recurrence.
This is neither a new operation-price table nor automatic complexity analysis.

Pure finite ranges can reuse their generated guard/body correspondence directly:
`while_range_encoded` supplies the exact native range-count descent internally,
including empty ranges, positive dynamic stride and early function return.
The structure-valued `StructuredRange.sum` consumer infers its complete function
bound around that rule. Uniform component bounds remain proved compiler
budgets, not assumed prices for native mathematical operations. General
data-dependent loop bounds still need the author's invariant or potential.

**Array-task integration:** the shared
[`ArrayFunction`](../Complexity/Language/ArrayFunction.lean) interface selects one
declared `Buffer Nat → Nat` source function. `Correct valid answer` states ordinary
`Array Nat` input/output correctness and successful termination without resources;
the [RAM `TimeO` interface](../Complexity/Computability/Ram/Compiler/Language/ArrayFunction.lean)
uses that same implementation and the existing allocation-aware execution result.
It fixes input layout and a logarithmic input-width scale, permits one uniform
constant width factor, and requires actual executions for every legal input at
every admitted width. Capacity is proved for those executions, not a premise
that silently excludes inputs. Its bound uses mathlib `IsBigO`.
This is a preloaded single-array/natural-result interface, not general I/O,
input loading, a persistent pure container API or a replacement cost semantics.
The interface and actual RAM connection are checked; existing clients can reuse
them through the fixed-type program wrapper below.

**Fixed-type program wrapper — checked:** `Complexity.Program Input Output`
selects the same typed source function with externally fixed input and output
representations. `Correct valid post` accepts an ordinary mathematical relation;
`TimeO valid size growth` keeps the task's size measure explicit and uses the
existing actual RAM execution. The source wrapper, scalar and multiple-array
inputs, structural outputs and compatibility with `ArrayFunction` are checked.
The [typed-program consumer](../Examples/Language/Program.lean)
publishes an existing two-argument source function using its generated total
contract and ordinary mathematical equation. `Correct.of_functionTotal` supplies
the shared invocation bridge, without a second algorithm or environment adapter.
Registration must be fixed by the interface, not supplied by a candidate as free
preprocessing or answer decoding. Right-associated natural/Boolean array and
scalar inputs now compose in a shared layout: arrays append objects to the
existing heap, while scalars only prepend arguments. Old identities and contents
remain unchanged. The opt-in `Input.PrefixClosed` property
records exactly the preservation needed for composition; arbitrary custom input
relations are not silently assumed to have it. Physical initialization reuses
the same generic `ArenaRep.push_buffer` theorem as actual runtime allocation.

Standard `deriving Program.Input, Program.RamInput` and `deriving Program.Output`
register closed records through one checked direct-field embedding. The append
consumer has two array fields and an array-valued output record; its correctness
proof reuses the existing allocating source implementation and `Array.append`
contents contract. The supported ordered field tuple must already have a layout.
Parameterized/dependent/inherited records and general heap-backed datatypes are
not covered. Extending native source-record syntax to heap-backed fields remains
separate work: currently the record is a mathematical invocation interface and
the source function receives separate typed arguments. These wrappers do not
compile arbitrary Lean functions or derive resource proofs from correctness.

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
   Finish the shared array-task consumer and connect the existing
   [uniform time](../Complexity/Computability/Ram/Time/Basic.lean)
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

## Splay proof exercise — checked

Use one actual `source_program` splay implementation to challenge the interfaces
above. The selected representation uses three borrowed arrays for keys and left
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

The complete [source correctness proof](../Examples/Language/Splay/Correctness.lean)
and its callable total contract now check on 0v0, including the shortened
recursive branches. The proof uses one induction on the mathematical input tree,
with no time or capacity premise. Shared `source_eval` simplification replaces
the old per-example operational branch wrappers; recursive calls stay opaque
until their actual execution equations are supplied.

The complete [instruction bound](../Examples/Language/Splay/Cost.lean) and
[halted RAM invocation](../Examples/Language/Splay/Compiled.lean) now check too.
Their fixed coefficient comes from the compiler and covers the actual recursive
calls, field operations, branches and outer call/return/halt overhead. Shared
finite-word realization handles the copy/compare/read/write/call fragment.
The represented-tree interface derives all three column-index bounds from its
successful reads; clients need not carry another copy of those access proofs.
The [consecutive-call theorem](../Examples/Language/Splay/Sequence.lean) constructs
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
   shares publication with independent mathematical specifications. Indexed calls
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
   Reuse source totality and actual heaps without another per-program termination
   proof. A shorter public theorem must not hide an equally long private
   connection proof.
2. Preserve native finite-range correspondence and inferred uniform budgets.
   Improve generated mathematical equations so ordinary fold/product proofs
   need less local-tuple projection; extend construct combinations only with
   matching real consumers. Dependent bounds, recursion descent and algorithmic
   potentials remain mathematical obligations, not guessed annotations.
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
