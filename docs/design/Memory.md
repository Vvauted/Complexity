# Heap, allocation and lifetime

A heap view preserves actual aliases. Allocation extends placements for live roots;
scoped reclamation restricts the current heap, not its entry-time contents.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Abstract objects, not renamed addresses

The source heap contains typed objects with ordinary mathematical contents.
A buffer view identifies an object, offset and length. Slices of one object may
overlap and observe each other's writes. Neither copying a handle nor forming a
view copies the contents.

Initial implementations operate on supplied objects and scratch storage.
Source-level read/write/view and frame laws use upstream collection facts.
The backend heap relation maps objects to physical regions and views to actual
descriptors, reusing `ArrayRef.Rep`, indexed representation and slice/frame
lemmas. Distinct allocated objects have disjoint realizations; distinct handles
need not denote distinct objects. An import must preserve actual input aliases.

Initial aliases must agree on the scalar type of the underlying object. There
is no unchecked pointer reinterpretation: overlapping views cannot silently
import the same cells as unrelated Nat and Bool objects. Cross-type views need
an explicit verified conversion/representation rule before they are supported.

The independent [heap foundation](../../Complexity/Language/Heap.lean) now supplies
typed native-array objects, offset/length views, checked read/write/slice
operations and read-after-write/alias/frame laws. A successful write is proved
to be an actual native `Array.set` at the object and cell levels. This foundation
is carried by the source execution state, including across calls and faults.
`Buffer.Contents` observes a valid view as an ordinary native array and transfers
reads and writes to `getElem` and `Array.set`, including updates through aliases.
Read/write/slice statements now invoke these same operations; calls retain their
actual updated heap. `Buffer.Disjoint` uses different objects or disjoint mathlib
`Set.Ico` intervals within one object. `Buffer.PreservesOutside` preserves the
contents of initially valid disjoint views; successful writes establish it, and
it composes through intermediate heaps and permits interval enlargement. This
is not ownership of handles, whole-heap equality or a ban on overlapping aliases.
The named traversal exports this relation with its array result through the
source function contract and the same actual compiled invocation.
[`buffer_frame`](../../Complexity/Language/Heap/Tactic.lean) now closes routine
logical consequences of these supplied observations with local Aesop rules.
It uses existing separation facts in either orientation, not object inequality
or a global no-aliasing assumption. Both the two-buffer caller and allocating
append reuse it; array identities, footprint inclusion and new separation
proofs remain explicit. Direct and imported resource proofs use the same frame
finish for their second call, retaining the original ranges, launch conditions
and instruction bounds. General indexed-traversal frame inference is unfinished.

A checked [source-frame rule](../../Complexity/Language/Effects/Heap.lean) uses `Stmt.NoCellWrites`
for the statement and all callees yields `Exec.heap_prefix` and
`Exec.contents_frame` for the actual final heap, including faults. Contents
transport uses [`Buffer.Contents.mono_prefix`](../../Complexity/Language/Heap/Prefix.lean)
and `List.IsPrefix`; fresh initialization is allowed, but explicit
cell writes are conservatively excluded. This is contract bookkeeping, not
automatic inference of mathematical ranges, capacities or loop invariants.

The same source program now includes `boundedMapPair`, two ordinary calls to
the existing traversal. Its contract gives both mapped arrays and preservation
of every initially valid view disjoint from both. The two inputs must be disjoint
for this independent-map specification, but may be slices of one object. This
is not a global no-alias restriction. Its
[compiled invocation](../../Examples/Language/TraversalCompositionCompiled.lean)
reuses the callee's correctness, realization and cost bounds at the actual
intermediate heap. The stack bound covers the pair, traversal and increment
helper; the independent linear instruction bound counts both traversals and
their real invocation/sequence overheads.

The [borrowed-buffer representation](../../Complexity/Computability/Ram/Compiler/Language/Heap.lean)
fixes an object-to-base placement as proof data, represents each complete object
with the existing `Source.ArrayAt`, and observes views through the existing
two-field `ArrayRef` convention. Placement is not a runtime object table.
Its read and write rules reuse `ArrayAt.slice`, native-array store rules and
indexed frames; they separate actual cells of different objects, not overlapping
views of one object. The same register layout now indexes typed fields, with
generic argument packing and receiver proofs. Passing buffer fields and actual
updated heaps through the whole compiler is now proved. A view encoding
need not recover source handle identity: empty views of different objects can
share an encoded endpoint.
Do not infer handle equality from descriptor equality or assume that a successful
access simulation also implements and charges fault checks.

The [operation bridge](../../Complexity/Computability/Ram/Compiler/Language/HeapOperation.lean)
connects a successful source read or write to real RAM load/store expressions,
their exact endpoints and the existing compiler-derived instruction counts.
Operand expressions are evaluated dynamically; placement is only a proof
parameter. The source statement cases use these shared rules, and the whole
simulation and runner connection retain the same actual final heap.

Use relations when abstraction forgets storage details; do not require a
bijection between an entire RAM heap and an observed list. Update related views
through the current heap and operation effects, not through obsolete snapshots.

## Selected initial allocation protocol

The typed core now supports fresh initialized objects as well as supplied ones.
The monotone allocator primitive, initialized-prefix proof, callable RAM runner
and source-heap representation connection are now implemented in
`Memory/Arena` and `Compiler/Language/Arena`. Source `Heap.alloc`, heap shape and
root preservation, and placement transport are also checked. The primitive body
uses `14 * length + 14` instructions; its preloaded function call including
return and halt uses `14 * length + 69`. Session bootstrap separately uses three
instructions. These are costs of the actual emitted code, not host allocation.
The same allocator is parameterized by its five local registers; the inline
typed-operand connection uses `14 * length + 18` instructions, including its
two real operand assignments. It proves the new heap representation and
returned lexical binding at the same execution endpoint. This reuses one
initialization proof and adds no function-table entry.

`Stmt.alloc` now has independent source semantics, its real evaluator,
budget-free correctness and VCG rules, source linking and syntax-directed
lowering. The checked general measured simulation composes allocating bodies
through loops and recursive calls, retaining the actual final heap, extended
placement and cursor. `ArenaReady` and `ArenaExecutionCost` describe the same
source `Exec`; the latter observes actual lowering costs, not a budget required
by source correctness. `FunctionArenaRealizable` packages separate range,
nesting and cursor-dependent capacity conditions and reuses an independent
`FunctionTotal` contract. The [runner connection](../../Complexity/Computability/Ram/Compiler/Language/Arena/ProgramExecution.lean)
reaches the halted invocation with positive word width, rooted represented
arguments and sufficient code/stack capacity. Its body count adds two
private-flag instructions, then the actual outer call/return and halt overhead;
input preparation and the one-time bootstrap remain separate.
The checked [allocation consumer](../../Examples/Language/Allocation.lean) calls
an allocating `make`, allocates again, then reads the first array when nonempty
and returns it. `retain_runUntil` retains the actual runner count, final arena
and original `ArrayRef` contents, including the empty case. Its `Named.make`
uses `Buffer.alloc`; `named_make_spec` proves ordinary `Array.replicate` contents
with `mvcgen`, without source capacity or time premises. Mathematical ranges
and loop/recursion arguments remain author work; register/placement transport
uses the shared proof. Allocation-aware resource linking transports the same
readiness and costs; the source-frame rule preserves old contents for bodies
without cell writes.
The caller/session owns the live arena; nested calls share allocation progress.
A function return alone does not reset it; an explicit scratch scope has the
lifetime behavior described below.
Caller-supplied scratch remains useful but does not replace fresh results.

The local call bridge now permits different input and output placements and
preserves the caller's rooted descriptors. Legacy heap-mutating imports can
reuse the final heap representation with an explicit metadata frame and final
object-shape containment. These checked boundary rules do not infer metadata
safety from arbitrary `SafeExec`. The separate checked `Arena.Linking` rules
transport readiness and exact costs through typed source embeddings.

At the source level, allocation appends a typed array of the requested length
and initial scalar value, returning the view `(old object count, 0, length)`.
The new object's identity is fresh even for length zero. Source allocation is
abstract and independent of RAM capacity; the corresponding target-success
theorem requires sufficient storage. No compiled out-of-memory result is
promised. A future fallible operation needs its own source/result semantics,
failure behavior and ownership/effect contract.

Growth needs two distinct laws. A single allocation preserves the exact
contents of every old object and supplies the fresh view's `Buffer.Valid` and
initialized-contents facts. The `Heap.ShapeExtends initial finish`
relation instead says that the object domain grows and every old object keeps
its scalar type and length; it deliberately allows changed contents. General
allocating execution proofs must preserve this shape relation, not an exact
contents prefix. It is already proved for the current source `Exec` and for the
standalone heap allocation operation. These are not physical-address claims.

The allocation-aware handle invariant is `Rooted`: a buffer's
object identifier is below the current heap's object count. It is weaker than
`Buffer.Valid`; it does not assert the expected scalar type or a valid view
extent, and does not ban aliases. Track it for live lexical values, suspended
caller environments, actual arguments and returned values. Fresh allocation
establishes validity and rootedness; writes and growth preserve the rootedness
of old handles. The existing checked-access conditions still decide type,
extent and index validity.

This boundary matters because public `Buffer` values can name future IDs even
though the frontend has no ID constructor. Such an old descriptor cannot be
transported through arbitrary placement extension: allocating its future ID
could change its encoded address. The allocation-aware interface states
its rooted-input condition explicitly and preserves it through execution.
Existing no-allocation theorems retain their admitted inputs; they do not acquire a hidden `Rooted`,
full-validity or no-alias premise.

Placement remains proof data, with no runtime object table. One allocation
extends it at the fresh ID with the actual old cursor address and leaves every
old ID's placement unchanged. Agreement on old IDs preserves `bufferRef`,
`valueWords` and environment/register matching for rooted values. This
transport needs no additional offset non-wrapping premise: it preserves the
same existing word encoding, including unused wrapped endpoints. Length and
scalar-operation ranges remain the separate `ValueFits`/realization obligations.
The general allocating simulation returns an existential final placement
extending the initial one, an actual final heap representation, and return
fields encoded with that final placement. A continuation uses this same
post-placement and heap, including when restoring its suspended caller roots.
The fixed-placement certification branch and public results remain for the
no-allocation subset; adding allocation to realization while leaving the old
fixed-placement theorem universal would be unsound.

The initial target protocol reserves RAM address zero for the shared bump
cursor. This is an opt-in arena convention, not a restriction on old RAM
programs. `ArenaRep placement next heapLimit heap target` wraps
the existing `HeapRep` and requires:

- `1 <= next <= heapLimit < 2^w`, with `target.mem 0` the exact word encoding
  of `next`;
- every actual represented object cell has a positive address strictly below
  `next`, leaving `[next, heapLimit)` available for fresh cells;
- the existing object scalar ranges and actual-cell separation. Empty objects
  require no distinct cell or stricter unused-address condition.

This is a prefix reservation, not a compactness requirement: holes and retained
input storage may occur below `next`. `heapLimit` remains the fixed heap/stack
boundary, while `next` is changing allocation progress. Source handles are
still object IDs; the returned RAM buffer is still a base/length descriptor.

The arena/session bootstrap initializes the metadata cell once with an actual,
charged store; it does not run again at each function entry. Preloaded input
contents remain subject to the declared loading boundary, not an implicit free
copy or relocation. An allocation lowers to ordinary existing RAM/IR operations:

1. Read the current metadata cell, obtain `base = next`, and compute
   `end = next + length` under the capacity condition `end <= heapLimit`.
2. Store `end` in the metadata cell to reserve `[base, end)`, then initialize
   each cell with the encoded scalar using actual counted stores and a loop.
3. Only after initialization, expose the base/length fields to the continuation
   and establish the complete appended-object representation.

Initialization invokes no user code and publishes no half-initialized source
object. Its intermediate prefixes use a pending-region/initialized-prefix
invariant, not the complete new-object `HeapRep` before all cells are initialized.
The metadata observation records reserved space even during this initialization.
Length zero reserves no data words but still has the actual metadata/descriptor
overheads of the selected code. The measured theorem derives initialization,
loop, cursor and descriptor costs from that emitted code, not charging a host
`Array.replicate` as a constant-time operation. Fresh temporaries also contribute
to the generated function's local-register and stack-frame bounds.

The current ABI restores caller registers but retains the callee's actual
shared memory; a cursor in that memory therefore survives calls without adding
hidden parameters/results or a new machine-state field. Each subsequent
allocation rereads it, rather than using a cursor cached before an intervening
call. Top-level repeated calls likewise use the actual returned shared state
and final placement. They never reconstruct entry memory or rerun bootstrap.

Metadata protection is an additional invariant, not a consequence of
`SafeExec`: ordinary safe RAM stores may still target address zero. Compiled
source object operations prove that their actual accesses avoid the
metadata. A raw legacy import needs a proved metadata frame, or an
allocator-aware postcondition returning the updated arena representation;
`HeapRep` and an address-capacity bound alone do not suffice. All cooperating
allocating imports use the same session protocol.

Without explicit reclamation, capacity covers retained inputs, metadata and
cumulative fresh allocation across nested and subsequent calls. A separate
stack bound must fit below `2^w`. Returned contents remain mutable through
aliases: a return-time contents contract does not promise an immutable value
forever. Resizing, arbitrary `free`, GC and reference counting are not implemented.

## Scoped scratch storage

`with_scratch do ...` lowers to the typed core's `Stmt.scope`. It is a lexical
control block, not a function or a value-producing return boundary. Ordinary
fallthrough continues after it; a `return` finishes the enclosing value block,
or the function if there is no value-block boundary, after leaving intervening
scratch scopes through cleanup. Allocate a result outside the scratch scope when it must
survive that scope, and use temporary buffers inside it. This does not implicitly
copy, move or freeze a returned buffer.

`ScopeSafe initial finish control` requires every surviving local handle and
returned handle to refer to an object already present at entry. It is a
root/lifetime condition, not a disjointness, contents or full-view-validity
condition. Mutable buffers contain only scalar Nat/Bool cells. Immutable nodes
have explicit typed tails, and represented heaps require those links to point
to earlier objects: keeping a root's prefix therefore keeps its whole chain.
Node references are source-language values, including inside products and
options. Their rootedness checks the entry object domain; it does not by itself
certify a typed lookup or a valid complete list. Integrating node construction
and reads must retain the backward-link invariant and this reachability
argument. Arbitrary mutable pointers and closures are not covered by the
current scope interface.

On a safe finite exit, the source retains
`finish.heap.take initial.objects.size`: the prefix of the **current** heap.
Writes to old objects and outer locals remain visible. Only objects allocated
inside the scope, including through its callees, are removed, so later allocation
may reuse their identities. This rule also applies to a safe fault exit and
preserves that fault. If the entry-root condition fails, the source retains the
full current heap; normal completion or
return becomes `Fault.regionEscape`, while an existing fault is preserved.
The semantics does not silently leave dangling handles or roll back earlier writes.

`TotalWP.scope` and `scope_compose` prove successful exits from a body contract
that supplies non-escape and the postcondition on this restricted final heap.
The native `Stmt.scope_action_spec` composes the same endpoint conversion with
the body action. Named scratch blocks expose their actual body, equation,
continuation and safe-exit `spec`; no second evaluator determines cleanup.

Inside a value block, named scratch boundaries additionally expose `Visible`,
`body_completion_contract` and `completion_contract`. Their normal and local-return
relations mention only visible source variables and the actual endpoint heaps.
`completion_spec` applies such a contract to the existing action in `mvcgen`;
`completion_contract_of_body` discharges the scratch boundary once the visible
locals and any local result are rooted in the entry heap. Complete locals are
reconstructed using a frame theorem about that same execution, not an assumed
inverse of the projection. The Unit-valued worker in `Examples.Language.Scope`
uses this interface for both nested scopes. Local-return `while` uses the
corresponding visible guard/body contracts and `completion_rel_contract`.
The shared well-founded rule asks for preservation and decrease only on
continuing rounds; completion uses the real masked guard to leave the loop.
`Scope.make` exercises a reachable loop-local return and retains its same-source
RAM workspace guarantee. Visible tuple/state-relation construction and
mathematical-local interfaces for richer loops and ranges remain open.

The RAM lowering saves the actual cursor from address zero in one fresh local,
runs the body, then stores that saved cursor back. Capture and release each
execute three instructions; the latter runs even when the body sets the return
flag. Release does not clear cells or restore old data. The representation proof
keeps precisely the retained source objects and makes the suffix available to
subsequent allocation. `ArenaReady.scope` certifies only safe exits. There is no
compiled escape scanner or claimed runtime implementation of `regionEscape`;
successful target execution remains conditional on non-escape and capacity.

Space must cover every intermediate execution, not just the restored final
cursor. Nested scratch regions contribute their simultaneously reserved space;
sequential reuse need not add their allocation totals. The allocation-aware
memory interface bounds actual accessed addresses by the heap/stack envelope.
That is a sufficient physical workspace bound, not an exact peak-reachable-space
metric. Register, code and I/O storage are separate. The
[source consumer](../../Examples/Language/Scope.lean) allocates one result outside
two nested scratch regions, writes it and returns early through cleanup. Its
[compiled theorem](../../Examples/Language/ScopeCompiled.lean) repeats that worker
arbitrarily many times within word ranges, returns the same mathematical result,
and bounds every actual access by `entryCursor + 1 + 2*n + 2*frameSize`, independent
of repetition count. The existing source loop proof supplies termination;
resource readiness does not require a second descent argument.

## Allocation and lifetime milestone

**Status:** typed source allocation, its correctness/evaluator rules, general
measured simulation through loops and recursive calls, and the halted runner
connection are checked. Named `Buffer.alloc` and the complete allocating client
are checked too, as is allocating resource-import transport. The complete
library, all Examples, the routine source-frame consumer and the complete manual
build. Scoped scratch reclamation, its named mathematical contracts and the
same-source repeated-call runner/physical-workspace theorem are now checked.
Arbitrary lifetimes and encapsulated persistent pure results remain open.
Develop this alongside the [function and mutable-contract milestones](../ROADMAP.md#m1--function-definitions-and-proofs-that-feel-like-lean);
it constrains what a pure-looking collection API can mean.
See the [scoped reclamation checklist](../RECLAMATION_TODO.md) for its concrete scope.

The first bottom-up layer is now implemented and individually checked:
[source heap allocation](../../Complexity/Language/Heap/Allocation.lean),
[actual RAM allocation](../../Complexity/Computability/Ram/Memory/Arena/Allocation.lean),
and the [typed runner connection](../../Complexity/Computability/Ram/Compiler/Language/Arena/Execution.lean).
They prove initialization, old-object preservation, cursor persistence and
compiler-derived costs. The same allocator now has a five-slot inline instance,
including typed operand materialization, and checked call-boundary rules for
placement extension and explicit legacy metadata frames. `Stmt.alloc` now has
source semantics, `TotalWP`/VCG rules, source linking and static lowering.
The [general measured simulation](../../Complexity/Computability/Ram/Compiler/Language/Arena/MeasuredSimulation.lean)
threads the same execution's final heap, extended placement and current
cursor through calls and loops; the [runner connection](../../Complexity/Computability/Ram/Compiler/Language/Arena/ProgramExecution.lean)
includes private-flag initialization and the outer call/return/halt cost.
Independent source correctness can supply termination to the separate readiness
proof. Positive word width, exact values, rooted represented inputs and
code/stack/arena capacity remain explicit conditions; input loading and the
one-time bootstrap are separate. The [allocation consumer](../../Examples/Language/Allocation.lean)
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

The [concrete protocol](Memory.md#selected-initial-allocation-protocol)
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
