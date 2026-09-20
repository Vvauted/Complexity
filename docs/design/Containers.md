# Container representations and operations

Runtime layouts, mathematical observations and callable operations are distinct
interfaces. This document states their implementation and preservation boundaries;
see [native composition](ContainerFrontend.md) and [resource composition](ContainerResources.md)
for clients of these operations.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Language and data coverage

The following is the author-facing scope, not a list of names to make the parser
accept. Each capability needs the same source declaration, checked mathematical
meaning, actual executable operations and a connection to the existing RAM and
resource proofs. Representation lemmas alone do not complete a frontend feature.

| Capability | Required end state | Current boundary |
| --- | --- | --- |
| Ordinary containers | Contiguous `Array α` and `Vector α n`, and an actual linked-node `List α`, with composable behavior and cost contracts for their operations | Actual Nat-buffer copy/append and Array contracts are checked. Immutable nodes have shared-tail contents and complete RAM representation. Callable List emptiness, uncons, cons and a real callback-based fold reach the same halted RAM execution and full invocation bounds. Fold accepts an arbitrary represented accumulator and retains the original list through callback effects. Native List declarations generate mathematical functions, real fold/cons calls and checked correspondence, including allocated List results, List-valued fold accumulators and imported allocating callbacks. The remaining operation library, general element layouts and a complete persistent container frontend remain open. The Buffer List view is explicitly named `bufferList`. |
| User-defined data | Ordinary structures, `Sum`, recursive trees/lists, constructors, projections and useful pattern matching | Closed structures with direct scalar/scalar-product fields have checked registration, construction, projection, named calls and native mathematical proofs. Both the loop-free consumer and structure-valued finite ranges with helper calls reach the same halted RAM result and full instruction bound under explicit range/capacity conditions. General mathematical-local loop automation, structure recursion/matching, nested structures, general sums and recursive allocation remain open. The default represented path separately supports general `while` over array-valued records using explicit state contracts. |
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

The shared allocating [`Buffer.Map.body`](../../Complexity/Language/Buffer/Map.lean)
now has a checked `Array.map` correctness theorem. Each iteration performs an
actual read, calls the selected source function and writes its returned value;
the mathematical mapper occurs only in the supplied contract. The proof retains
fresh output storage and all old contents, and permits a callback to allocate
while preserving old contents. Its checked
[`Buffer.Map.program`](../../Complexity/Language/Buffer/Map/Program.lean) adds an
actual callable entry through the existing program extension, preserving the
original callback and all of its calls. The checked
[`RAM connection`](../../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Execution.lean)
publishes the same fresh result and retained old contents, with initialized
allocation, actual per-element calls and final return included in the bound.
Its numerical interface separates the sum of callback bounds from linear
traversal overhead; a constant callback bound gives a proved size-only affine
bound. The checked [asymptotic interface](../../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Asymptotics.lean)
turns that same size-only budget into mathlib `IsBigO` in the input length,
without exposing its compiler coefficients to clients. This numerical theorem
does not discharge the actual invocation's word ranges or storage capacity.
The shared
[`scalar bridge`](../../Complexity/Computability/Ram/Compiler/Language/Buffer/Map/Scalar.lean)
reuses existing nonallocating `FunctionRealizable` and `FunctionCostBound` proofs
without another callback resource proof. Arena growth counts retained output
and permitted callback allocation, not exact peak live space. Frontend
registration remains separate work: this is not yet native `xs.map f` syntax,
dynamic closures or a persistent pure Array interface.

## Concrete layouts and callable operations

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
[`Heap.BackwardLinks`](../../Complexity/Language/Heap/Backward.lean): when actual
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
The [allocation bridge](../../Complexity/Computability/Ram/Compiler/Language/Arena/NodeExecution.lean)
now connects one actual cursor update and three stores to the fresh node,
complete arena representation and `head :: values` contents. The
[read bridge](../../Complexity/Computability/Ram/Compiler/Language/Heap/NodeExecution.lean)
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
[`List.IsEmpty`](../../Complexity/Language/List/Basic.lean) matches the actual
optional root, returns ordinary `List.isEmpty` and preserves the entire heap.
Its [compiler bridge](../../Complexity/Computability/Ram/Compiler/Language/List/IsEmpty.lean)
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
[`List.Uncons`](../../Complexity/Language/List/Uncons.lean) now supplies the next
callable operation: it matches the root, reads a present node once, and returns
the head and identical shared tail. Its independent correctness theorem refines
ordinary `List.head?`/`List.tail` observations at the unchanged heap. The
[compiler bridge](../../Complexity/Computability/Ram/Compiler/Language/List/Uncons.lean)
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
The [named client](../../Examples/Language/LinkedList.lean) writes the same operation
with `source_program`, optional-root matching and `ref.read`. Its generated body
is definitionally the public operation, so correctness and refinement reuse the
library theorems directly, without a per-client lowering adapter.

[`List.Cons`](../../Complexity/Language/List/Cons.lean) supplies callable construction.
Its independent source contract gives `head :: values`, the exact fresh root
and allocated heap, and preservation of all previously represented lists.
The checked [compiler bridge](../../Complexity/Computability/Ram/Compiler/Language/List/Cons.lean)
returns that same halted execution, the actual cursor increment of three words
and a full invocation bound including operand preparation, allocation, option
packaging and outer-call overhead. The named client writes `NodeRef.cons head tail`
and reuses the public contract by definitional equality. Its singleton also
infers the type of `none`; neither client supplies a register proof.
These root operations do not by themselves supply a native pure List API.

The shared [linked fold](../../Complexity/Language/List/Fold/Basic.lean) now follows
actual tail pointers with a `while` loop and invokes the selected source callback.
Its source correctness and [callable entry](../../Complexity/Language/List/Fold/Program.lean)
are checked on 0v0. The result refines ordinary `List.foldl` for an arbitrary
represented accumulator. The callback domain need hold only along the actual
mathematical accumulator trajectory. Callbacks may allocate or change mutable
buffers; old immutable-list observations survive by the shared heap-shape rule,
without an unchanged-heap assumption. Mathematical list induction supplies
termination without a time budget or recursive fold invocation.

The checked [fold RAM connection](../../Complexity/Computability/Ram/Compiler/Language/List/Fold.lean)
retains those same callback returns and final memory, separates
accumulator-dependent callback bounds from linear traversal work, and includes
outer call/return/halt. The traversal itself needs no length-dependent call
depth. The initial reservation interface sums callback allowances; it does not
yet distinguish retained growth from reusable scratch peaks. The checked
[numerical interface](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/Asymptotics.lean)
expresses callback charges as an ordinary `List.mapIdx` sum over `take`/`foldl`
prefixes. Uniform callback bounds give a size-only affine envelope and mathlib
`IsBigO` in list length. A nonconstant bound only needs the common envelope at
actually visited prefixes. These numerical facts do not discharge word ranges,
capacity or callback correctness. Native fold syntax should select the same
implementation through heap-indexed refinement, not force shared list layouts
through the scalar frontend's lossless `Equiv`. Native construction and List
function results and List-valued native fold accumulators use the relational
[native facade](ContainerFrontend.md); general element layouts remain unfinished.

The checked [native callback bridge](../../Complexity/Language/List/Fold/Native.lean)
accepts an allocating callback's actual evaluation and represented result through
`Contract.of_eval`; `eval_exists` retains the resulting accumulator, original
list and heap shape. Its pure specialization instead uses an injective
accumulator encoding and gives exact result and unchanged-heap equations from
the same generic fold contract. Neither route proves a second traversal or
requires a heap-independent encoding of lists. Existing callback
range and cost proofs similarly feed the fold through the shared
[finite-function bridge](../../Complexity/Computability/Ram/Compiler/Language/Arena/FunctionResources/Finite.lean).
The fold itself now exports [callable resource contracts](../../Complexity/Computability/Ram/Compiler/Language/List/Fold/Resources.lean),
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

## Node safety and observation contracts

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
the [relational facade](ContainerFrontend.md). The remaining traversal operations and general
element layouts remain open.

The shared action layer is checked in
[`Eval.Node`](../../Complexity/Language/Eval/Node/Basic.lean) and its
[`Verification`](../../Complexity/Language/Eval/Node/Verification.lean) rules.
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

## Representation and operation design

Mathematical equivalence does not select a suitable runtime data structure.
The default source `List` must be a real immutable singly linked list, with
element/next nodes, an empty reference and structural tail sharing. `cons`
allocates one node rather than copying the tail; `tail` follows the stored link.
Append copies the left spine and shares the right list. Its public behavior
reuses ordinary Lean List mathematics, while its cost comes from those actual
operations and the existing RAM allocator and compiler.

`Array` and length-indexed `Vector` instead use contiguous indexed storage.
An array may still have a List-valued mathematical observation, but that is an
explicit proof view, not the default implementation of the source List type.
`Representation.bufferList` and the Buffer copy/append List contracts are
such explicit array observations. The default `Representation.list` instead
relates an optional typed node root to its ordinary List contents at the actual
heap. Neither relation alone supplies native container syntax.

For fixed-size element representations, the linked structural operations should
support constant head/tail/cons bounds and traversal-dependent length/index/append
bounds. Element construction, copying, allocation and callbacks must be charged
where they actually occur. No constant-cost promise follows solely from a
container's mathematical name. Pure Array/Vector updates also need a proved
ownership/reuse or copying policy; borrowing mutable storage is not persistence.

The source heap now has distinct immutable node objects and typed optional
links. `Heap.cons` appends one node and shares its tail; `Heap.uncons` performs
actual typed lookup. `NodeRef.Contents` relates finite chains to ordinary Lean
lists and preserves shared tails under buffer writes and fresh allocations.
Backward links justify keeping the complete chain during prefix reclamation.

The RAM representation gives every node three words: head, tail tag and actual
tail address. Complete-object separation and arena reservation include these
words, and placement extension preserves stored links. The checked allocation
block loads the shared cursor, reserves three words and initializes them with
three actual stores. Its compiler-derived body count is 21 instructions; the
nonempty-node read performs three actual loads in 13 instructions. The same
measured endpoints establish the typed head/shared-tail contracts and preserve
the represented surrounding heap. These counts exclude operand materialization,
outer option handling and function setup/return. Typed node references now pass
through effectful parameters, returns, products and options, with their actual
address encoding and rootedness. `Stmt.readNode` now connects the actual lookup
to its source proof/observation rules, linking and both ordinary and
allocation-aware measured simulation. The effectful spelling is
`let (head, tail) ← ref.read`, after matching an optional root. The same read
can precede an allocating continuation. `Stmt.consNode` connects actual node
construction through source semantics, observation, linking and allocation-aware
measured simulation. The effectful spelling is `let ref ← NodeRef.cons head tail`.
It materializes three operand fields before the existing allocator, for a proved
27-instruction block before its continuation. Native cons construction and
List-valued results use the [relational facade](ContainerFrontend.md); the complete operation
library remains open.

The first complete callable node-root operation is `List.IsEmpty`: one actual
source body matches the optional root and returns a Boolean without reading a
node. Its ordinary `List.isEmpty` refinement preserves the entire heap. The
checked compiler bridge returns the same halted RAM execution and derives its
full invocation bound from the existing branch, return and call rules. Its
arguments and heap must have the supplied representation and fit the launch
capacity; preloading the inputs is outside that invocation boundary. Native
let-call bindings now accept `xs.isEmpty` and `List.isEmpty xs` for the supported
Nat/Bool Lists. Generated correspondence reuses this actual operation and its
unchanged-heap equation. The native `isEmpty` consumer has ordinary Boolean
correctness and a complete RAM invocation bound inferred from the callee and
caller instructions. Its composable arena readiness checks no node and needs
no physical heap representation or element range; the complete launch still
retains those representation/capacity conditions. This does not add call
hoisting inside arbitrary expressions such as an inline `if` condition.

`List.Uncons` also has a checked complete invocation: matching the actual root,
reading a present node and returning an optional head/shared-tail pair. Its
mathematical output is `xs.head?.map (fun head => (head, xs.tail))`, related to
the returned handles at the unchanged heap. The full constant bound includes
the branch, option packaging and outer-call overhead in addition to the node
read. It comes from the same source implementation and measured compiler rules,
not from assigning a price to the ordinary Lean List function. The native
frontend registers `xs.uncons` and `List.uncons xs` to this same operation;
these are source spellings, not a claim that upstream Lean defines `List.uncons`.

Its ordinary-parameter `arenaMeasured` entry composes the existing read at the
current heap from the represented list and the present head's range. There is
no whole-tail range check, physical heap representation or time-bound premise
in this readiness interface. A separate `arenaMeasured_of_heapRep` convenience
entry obtains the head range from an existing launch heap. Both preserve the
actual result, entire heap and cursor; independent cost certificates count the
same execution. The scalar-head, replace-head and conditional inspection proofs
reuse this entry, retaining actual intermediate heaps and constructor costs.
Complete halted RAM invocations still require their original launch conditions.

`List.Cons` supplies the corresponding complete construction invocation. Its
source theorem exposes ordinary `head :: values`, the exact fresh root and heap,
and preservation of previously represented lists, with no resource premise.
Its RAM theorem retains those facts for the same actual halted invocation,
the cursor advance of three words and a compiler-derived full invocation bound.
The bound includes operand preparation, node initialization, optional-root
packaging and call/return/halt. The named construction and singleton clients
reuse the public contract without a per-client machine proof. Source correctness
does not require finite target capacity; the RAM launch separately requires
the actual word ranges and three words of remaining arena capacity.

`List.Fold` now supplies a checked source traversal and callable entry. The
runtime uses a `while` loop, reads each actual node and calls the selected source
function with the accumulator and head. Its ordinary `List.foldl` theorem accepts
any existing accumulator representation, including heap-indexed representations;
the callback's domain is required only at reached mathematical prefixes. The
callback may allocate or modify buffers, while immutable-node preservation keeps
the original list observable. The proof's list descent is not runtime fuel or
a recursive fold call stack. Its checked RAM connection retains the same actual
result, final heap and cursor, with the sum of callback bounds plus linear
traversal and full invocation overhead. The initial arena bound sums callback
reservations along the mathematical trajectory; it is sufficient capacity, not
an exact peak-live-space claim or automatic reuse of scratch peaks.
The checked numerical interface exposes the callback contribution as an ordinary
list sum over `take`/`foldl` prefixes. Uniform per-callback bounds give a size-only
affine invocation bound and mathlib `IsBigO` in length, without another loop or
compiler proof. The common envelope is needed only at visited prefixes.

The shared node allocator bridge requires only that a nonempty tail belongs to
the existing object domain. A complete List contents proof is supplied only by
the List specialization; raw node allocation does not inspect or traverse it.

The shared native actions `NodeRef.consM` and `NodeRef.readM` already lift these
same heap operations into the existing exception/state monad. Their standard
`@[spec]` rules expose actual allocation or successful typed lookup. Separate
`consM_list_spec` and `readM_list_spec` rules reuse the linked representation to
supply mathematical cons contents, the identical shared tail and preservation
of old lists. Missing or wrongly typed reads retain the heap and report
`invalidObject`; construction does not validate its tail. The generated
`readNode` observation reuses `readM`, and `consNode` observation reuses `consM`,
so source proofs use these same native specifications. The persistent native
container frontend remains unfinished.
