# Native container composition

The frontend relates ordinary List values to actual shared node representations
at each heap. This is not a lossless decoder from handles or a persistent Array API.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Checked composition

The common [represented frontend](../../Complexity/Language/Syntax/Represented.lean)
generates ordinary Lean functions and node-backed source functions from one
`source_program` declaration. Existing `(native)` consumers retain their
compatibility naming layout. The checked
[linked-list consumer](../../Examples/Language/LinkedList.lean) includes a constant
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
correspondence. Initialization and field copies remain actual source operations.
Results containing a bare buffer or node use an optional join slot: the selected
branch stores a real result, and correspondence excludes the absent case before
the common continuation. No default pointer is fabricated. Represented
self-recursion is also checked, including allocation before the recursive call;
general patterns, mutual recursion and escaping callbacks remain separate work.
This does not restrict the
more general effectful fold library or change the existing `(pure)` path.

The same frontend also accepts `List.cons`, `head :: tail`, explicitly typed
empty lists and List-valued function results. The `NativeConstruction` consumer
allocates and returns a list, composes two list-returning calls, and folds both
the original input and its new extension after allocation. Ordinary List
equations specialize its generated `_refines` without a per-function heap proof.
The [constructor observation](../../Complexity/Language/List/Cons/Native.lean)
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

## Mathematical views, branches and recursion

The common preparation pass accepts ordinary mathematical List parameters and
results through the default entry. Existing examples retain `(native)` only for
their compatibility naming layout. Statically selected pure or imported native
callbacks use actual calls in `List.Fold.program`; `List.cons` and `head :: tail` select the
real allocating `List.Cons.program`. The same block generates an ordinary Lean function and
`_refines`; List handles are related to contents in the actual heap, not encoded
through an `Equiv`. A typed empty list needs no heap object.

Products and options can recursively contain these represented lists. Their
constructors, projections, parameters and returns compose the existing
heap-indexed relations. `NativeViews.inspectAndPrepend` returns an optional
head/tail observation together with a newly allocated list; the old observation
remains valid at the actual final heap. Preservation composes only for leaves
with a proved shape-extension rule. Mutable array contents and exact-heap
observations are not automatically persistent.

The linked-list consumer covers constant accumulators, reordered parameters,
immutable locals, consecutive folds and earlier same-family calls. Its
`NativeConstruction` family additionally constructs and returns lists, composes
two list-returning calls and folds both an old list and its newly allocated
extension. The generated `_action_rel_native` records a successful source result,
its representation in the actual final heap and preservation of old immutable
nodes. Each call transports retained list observations to its actual intermediate
heap through `Representation.list_mono`; no author-written heap adapter or second
algorithm is required. Read-only scalar results retain `_action_eq_native` with
the exact unchanged heap. Allocating functions do not receive that equation.
Native folds accept scalar/product or List accumulators. Their callback may be
an imported pure function or an allocating function from a completed native
family. The latter uses its heap-indexed correspondence, not an unchanged-heap
equation. `NativeLists.reverseAppend` folds an actual cons callback into a List
accumulator; the author's ordinary reverse/append proof reuses Lean's existing
fold/cons identity. Imported native calls, a preceding allocation and subsequent
use of the returned list are checked in the same consumer.

Explicitly typed List conditional bindings now compose those calls:
`let chosen : List Nat ← if flag then do ... else do ...`, with each branch
ending in a List return. The `:=` form uses the same path. Each branch may
allocate and call imported native functions, and a common continuation can
construct or fold the returned list. `NativeBranches.choosePrepend` and
`chooseSum` have checked ordinary mathematical equations and automatically
generated source correspondence on 0v0. The generated proof summarizes each
branch's actual result and heap before proving the common continuation once.
Source lowering uses the existing conditional, a local result slot and an
ordinary continuation; it adds no interpreter or heap-independent List decoder.
Only the selected branch executes. Initializing, assigning and reading the join
slot remain actual source operations for the separate cost proof.

The same binding interface supports `match` with exactly two List branches
(`[]` and `head :: tail`) or Option branches (`none` and `some payload`). List
matching calls the real Uncons operation before matching its returned option;
the head and tail projections are actual source operations. The branches retain
their selected heap and return to one common continuation. Both `←` and `:=`
forms use the supported result type; a branch may be a value or a do-block
ending in `return`. Results may be scalars, represented containers or their
supported products, options and closed records. `headOr` and allocating
`inspectOrPrepend` have checked ordinary equations,
generated source correspondence and end-to-end RAM theorems; `headOption` still
has only source correctness and correspondence. Join initialization and copies
remain real source operations. A result with a bare node/buffer field uses an
optional join slot: the selected branch supplies `some` of its actual result,
and generated correspondence excludes the absent case before the continuation.
No default pointer is fabricated. Preservation is composed only from proved
operation contracts.

`NativeViews.replaceHead` uses List matching and a subsequent constructor call.
Its ordinary equation is `replaceHead replacement values = replacement :: values.tail`,
proved by cases on the mathematical list. Generated relational correspondence
supplies the actual source correctness without another heap or traversal proof.
Self-recursion retains the same source function identity and relates recursive
arguments in the current heap. The linked-list `replicateAppend` consumer proves
its ordinary replicate/append equation after allocating before each recursive
call. One user termination hint is checked independently for the native function
and its generated relational correspondence; no budget proves termination.
General patterns, mutually recursive native families, general element layouts and escaping
callbacks remain open. The existing effectful fold library retains its wider
contract; this is not a complete persistent collection interface.

## Representation boundary

The native container frontend composes these heap-indexed operation contracts
at actual intermediate heaps. The existing pure-structure path instead
reconstructs a value from every raw layout using an `Equiv`, and proves an action
equal to `pure` with an unchanged heap. Neither mechanism applies to allocating
lists or to a list handle whose contents depend on the heap. Preserve that useful
scalar path alongside represented-operation correspondence; do not weaken its
purity claim or choose one arbitrary encoding of a shared list.
