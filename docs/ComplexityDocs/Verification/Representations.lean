/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.LinkedList
import Examples.Language.ProgramCompiled
import Examples.Language.ScalarCompiled
import Examples.Language.Strings
import Examples.Language.Traversal

/-!
# Represented data and collection contracts

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Relate mathematical values to the actual heap

The [shared representation interface](##Complexity.Language.Representation)
relates mathematical data to actual source values at the current heap. It
composes products, options, sums, subtype views and native scalar arrays/lists/vectors.
The [represented function contract](##Complexity.Language.RepresentedFunction)
can observe a returned value or an original argument at the final heap; an
in-place function returning `Unit` can therefore have an ordinary array output.

The existing [traversal](##Examples.Language.Traversal) supplies
`boundedMap_refines` once from its implementation proof. Its
`boundedMap_preserves_length` then follows just from the ordinary `Array.map`
size theorem through `Refines.of_math`, without another loop proof.
The [execution connection](##Complexity.Computability.Ram.Compiler.Language.RepresentedFunction)
applies that correspondence to the same actual RAM result and final heap.
It does not create a second run or change its independently counted costs.

These are call contracts on represented inputs, not constructors for every
mathematical value. They neither make the frontend accept arbitrary native
types nor turn a return-time buffer observation into a permanently immutable
array. Native type/operation registration and container ownership remain
separate language work.

For a pure registered representation, `Refines.of_encoded_eq_pure` consumes
the checked source equation at encoded native arguments and results. It builds
the shared refinement contract without a new execution induction or an inverse
on invalid raw values. Constructor/projection correspondence remains a compiler
obligation; an encoding declaration alone cannot justify a native operation.

For word-range transport, the backend's
[`RepresentationFits`](##Ram.LanguageCompiler.RepresentationFits) certificate
says that every actual value related to the mathematical value at its current
heap satisfies `ValueFits`. Its one-way `ofEmbedding`, `array`, `prod` and
`comap` rules compose supplied range facts for existing representations; they
do not select a canonical handle, add an encoder or establish that a represented
value exists. Apply the certificate to a real observation with
[`RepresentationFits.valueFits`](##Ram.LanguageCompiler.RepresentationFits.valueFits)
as `RepresentationFits.valueFits certificate observed`.
The array rule needs only a mathematical length bound and establishes descriptor
`ValueFits`, not element ranges, rooting, address bounds or allocation capacity.
Products use both observations at the same heap and permit shared storage.
These are explicit proved certificates, not typeclass inference or new syntax.

## Signed scalar expressions

The default `source_program` frontend uses ordinary `Int` parameters and
results for addition, subtraction, multiplication, negation and ordered comparisons. These
select the existing [integer source operations](##Complexity.Language.Scalar.Int),
not host-side arithmetic callbacks. For example:

```lean
source_program Signed where
  def distance (left : Int) (right : Int) : Int := do
    let delta := left - right
    if delta ≤ 0 then
      return -delta
    else
      return delta
```

The [checked scalar consumer](##Complexity.Language.Examples.Scalar.signed_distance_eq)
proves `Signed.distance_model left right = |left - right|` with ordinary
integer facts; generated `_refines` transfers it to the actual source function.
Subtraction invokes negation and addition. `<`, `>`, `≤`/`<=` and `≥`/`>=`
reuse the comparison call and, where needed, Boolean negation. Strict nested
operands are evaluated from left to right, including before a comparison
reverses its operands. Conditional calls stay in their selected branches;
a while guard is evaluated again on every iteration.

Literal arithmetic uses known binding, result and callee-parameter types;
it does not silently coerce a `Nat` variable to `Int`. Signed division,
remainder and equality syntax are not provided by this connection.
Calls beneath `&&`/`||` are not lifted out of their short-circuit branches.
The existing [RAM implementation](##Ram.LanguageCompiler.Scalar.Int)
charges the same source bodies, including sign branches and intermediates.
The scalar consumer's `signedDistanceCost` composes their existing certificates
to infer a uniform bound for this same caller, including its actual instructions.
Likewise, `Signed.squaredDistance` returns `delta * delta`; its ordinary
mathematical theorem states `(left - right) ^ 2`, and `signedSquaredDistanceCost`
composes the same subtraction and multiplication implementations. Multiplication
needs a word bound on the product of incremented representation fields, covering
intermediates even when the final result is zero. This is bounded-word integer
arithmetic, not a constant-time arbitrary-precision multiplication primitive.
Word ranges, call overhead and a complete caller's resource bound remain
separate proof obligations; correctness is not conditional on a time budget.

## Contiguous arrays and copying

The [buffer copy library](##Complexity.Language.Buffer.Copy) contains actual
`copyInto`, allocating `copy` and allocating `append` implementations. Their
contracts state ordinary Array contents and preserve observations of old views.
`copyInto` requires disjoint source and destination views, not different object
identities; disjoint slices of one object are permitted. Allocating `append`
allows its two inputs to overlap because the destination is fresh. These
operations currently store Nat cells and return mutable borrowed handles.
The contents theorem does not make their results permanently immutable or make
copying free in the separately proved RAM cost.

The [copy-loop cost](##Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.CostBound)
reuses the same source invariant and named loop contracts. The
[allocating append bound](##Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendCost)
includes initialization and both copying calls at their actual intermediate heaps.
Its independent [measured execution](##Complexity.Computability.Ram.Compiler.Language.Buffer.Copy.AppendReady)
retains the fresh destination, old contents and exact cursor growth. The bound
is affine in total input length; the complete
[record-program consumer](##Examples.Language.ProgramCompiled) additionally
includes field operations, packing and invocation overhead and proves uniform
`Program.TimeO` without a capacity precondition on the input arrays.

The [collection contracts](##Complexity.Language.Buffer.RepresentedCopy)
reuse those same implementations for Array, List and length-indexed Vector
views. For example, `append_list_length` combines `append_list_refines` with
`List.length_append`; the caller supplies no new loop proof. The
[resize implementation](##Complexity.Language.Buffer.Resize) allocates a new
buffer with the requested prefix and zero padding, retaining all old views.
It neither moves the original object nor changes an old handle's length.

## Arrays of product elements

[`Representation.arrayProd`](##Complexity.Language.Representation.arrayProd)
observes an ordinary `Array (α × β)` through two component array representations.
Both columns correspond to the same full array; mismatched lengths cannot denote
a truncated zip. The mathematical representation composes recursively and permits
aliases, but this does not supply arbitrary nested-element operations.

The [scalar-pair read](##Complexity.Language.Buffer.Prod.read_eval) executes two
real indexed reads and constructs the returned pair, preserving the entire heap.
Its [compiler bound](##Ram.LanguageCompiler.Buffer.Prod.read_costBound) counts
the handle projections, reads, pair construction, return and function initialization.
It requires an in-bounds row; RAM readiness and call overhead remain separate.
Fixed `Program` input and output layouts compose the actual column layouts.
`Input`/`RamInput` deriving accepts record fields such as `Array (Nat × Nat)`;
the supplied source and physical representations refer to the same preloaded
columns, not an executable preprocessing pass.

The represented frontend accepts arrays of pairs whose components are `Nat`
or `Bool`. Ordinary `.size` observes the first column's proved common length.
[`Array.getD`](##Complexity.Language.Buffer.Prod.GetD) checks that length before
reading either column, returning the complete fallback pair out of bounds.
Its source correspondence preserves all prior contents, including aliases;
the [compiled bound](##Ram.LanguageCompiler.Buffer.Prod.GetD) uses the larger
branch, including the bounds check and function initialization.

The [typed consumer](##Complexity.Examples.TypedProgram.pairLookup_correct)
uses record fields and ordinary array mathematics. `program%` inserts actual
field-packing instructions and automatically rearranges the existing input
observations; that packing is real source code, not a free cost conversion.
Returning a pair array observes the actual returned column handles.
Updating independent fields additionally needs separation or a proved alias-aware
contract: allowing shared columns for reading does not justify arbitrary `Array.set`.
Nested element operations and arbitrary pair-array allocation/copying are not
provided merely by the compositional mathematical representation.

## Arrays of optional elements

`Array (Option Nat)`, `Array (Option Bool)` and `Array (Option Int)` retain
ordinary optional values in their mathematical contracts. Their fixed
[`arrayOption`](##Complexity.Language.Representation.arrayOption) representation
has a presence column and the existing payload columns; an absent payload is
canonical, and `none` is distinct from `some 0`. All columns observe the full
array at the same actual heap, including its length. Integer payloads reuse the
canonical sign/magnitude columns.

The frontend supports ordinary `Array.replicate`, `.size` and `.getD` for these
layouts. Generated source code branches to pack the initializer or fallback,
calls the existing scalar allocators/readers for every column, and branches on
the read presence flag to return the optional value. These are actual source
instructions and calls, not free mathematical conversions. Allocation preserves
existing array contents; a defaulted read preserves the whole heap and returns
the supplied optional fallback out of bounds.

The [composite-array consumer](##Examples.Language.CompositeArrays) states its
correctness with ordinary `Array.replicate` and `Array.getD` equations using
`program_correct`. Its optional natural-array allocator also has an inferred
linear RAM body bound counting the packing branch and both column calls,
conditional on actual arena readiness. Fixed `Program` input/output and RAM input layouts use these
same columns. This does not yet supply optional-element mutation, arbitrary
heap-backed option payloads or a complete whole-program resource certificate.
Nested arrays of optional elements do not yet have a generated row reader.
Reading permits aliases; updating separate columns still needs separation or
an explicit alias-aware update proof.

## Canonical nested-array intervals

Canonical ragged storage retains a boundary buffer and a flattened payload.
The [interval extraction](##Complexity.Language.Buffer.Ragged.Extract) operation
reads the two endpoints, copies the selected boundaries minus their first
offset, and borrows the corresponding payload slice. The mathematical result
is ordinary `Array.extract`; its source contract requires ordered, in-bounds
indices. Even an empty interval retains one zero sentinel. It does not clamp
invalid indices or pretend that an absolute boundary slice is already rebased.

[`Rebase.copy`](##Complexity.Language.Buffer.Rebase.copy) performs that actual
allocation, read/subtract/write loop. Its
[compiler cost](##Ram.LanguageCompiler.BufferRebase.copy_arenaCostBound) includes
initialized allocation, copying, call dispatch and function setup, with an
affine envelope in the number of boundary cells. This conditional cost needs
an actual ready arena execution; it does not itself establish word ranges,
capacity or `Program.TimeO`. The enclosing
[extractor certificate](##Ram.LanguageCompiler.Buffer.Ragged.Extract.extractNat_arenaCostBound)
also counts both endpoint reads, both borrowed slices, the real imported call
and function setup. Its affine bound uses `stop + 1 - start` boundary cells,
not the number of payload cells; the Boolean extractor has the same interface.

The [rebasing readiness](##Ram.LanguageCompiler.BufferRebase.copy_arenaMeasured)
reuses the source loop's correctness and termination, adding the ranges of the
actual reads, subtraction and writes. Its cursor grows by exactly the input
length, and all old contents observations survive. Natural subtraction may
truncate at zero; the worker does not assume every cell exceeds the base.
The [extractor readiness](##Ram.LanguageCompiler.Buffer.Ragged.Extract.extractNat_arenaMeasured)
composes both endpoint reads and borrowed slices with that actual allocating
call. Natural and Boolean payloads retain ordinary `Array.extract` at the final
heap and reserve exactly `stop + 1 - start` cells, including the sentinel for
an empty interval. Boundary-buffer and flattened-payload lengths must fit the
selected word width, and the arena must have the stated remaining capacity.
Payload values are neither read nor copied, so they need no value-range premise.
These measured witnesses reuse the actual compiler count without choosing a
budget; the cost certificates above bound that same execution. Physical launch
conditions and complete caller `Program.TimeO` proofs remain separate.

The [three-level row operation](##Complexity.Language.Buffer.Ragged.Nested)
uses that extractor for in-bounds natural or Boolean rows. Out of bounds it
returns the entire supplied fallback without allocation. Both branches preserve
every old contents observation; the payload remains aliased mutable storage.
In bounds, the actual final heap contains new boundaries and the operation is
not a constant-time borrowed row lookup. Its
[callable cost](##Ram.LanguageCompiler.Buffer.Ragged.Nested.getNat_arenaCostBound)
has a proved linear envelope in the selected row's length, including its final
sentinel; out-of-bounds selection has a fixed envelope independent of the
fallback's length. The
[measured row read](##Ram.LanguageCompiler.Buffer.Ragged.Nested.getNat_arenaMeasured)
follows that same bounds check and imported extractor. Its exact allocation is
the selected row's length plus one sentinel in bounds, and zero out of bounds,
even when the supplied fallback is nonempty. The Boolean reader has the same
contract. The corresponding
[resource contract](##Ram.LanguageCompiler.Buffer.Ragged.Nested.getNat_arenaResources)
derives size ranges from the caller's argument ranges and relates readiness to
that caller's actual source execution. Both the mathematical result and preserved
old aliases refer to the final heap. Physical placement and enough remaining
arena capacity are still caller obligations, not consequences of a cost bound.
The reusable
[read and slice rules](##Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Buffer)
retain the actual access equations through allocating continuations. They
neither assert successful access nor manufacture arena readiness.
Ordinary composite `Array.getD`
threads this changed heap through subsequent column reads. Its generated proof
transports unread columns and the complete fallback to that heap, then preserves
earlier returned columns across later allocations. Supported record and product
views compose these same operations; string grids retain their original strings.
Unchanged-heap readers keep their exact-heap contracts; allocating readers expose
their actual final heap. Arbitrary-depth access, nested mutation and automatic
whole-reader RAM cost certificates remain separate work.

Typed `#[]` expressions construct empty arrays without an element initializer.
The frontend emits real initialized allocations for scalar and product columns,
including supported record, scalar-view and ragged layouts. Every ragged level
allocates its one zero sentinel and constructs its actual empty payload. No
dummy heap-backed element or extra fallback input is required. The mathematical
equation is ordinary `#[]`; old array observations survive the actual allocations.
For example, a record field of type `Array String` can use `let rows : Array String := #[]`.
This does not implement positive-length replication of heap-backed elements or
make construction and boundary rebasing free in the RAM cost model.

## Strings and character-indexed operations

[`Representation.string`](##Complexity.Language.Representation.string) keeps
ordinary Lean `String` values while storing their complete Unicode scalar
sequence in a contiguous natural buffer. It retains embedded null characters
and does not restrict or compress an application's alphabet. The descriptor
counts characters, not UTF-8 bytes; a character index cannot be substituted for
Lean's `String.Pos.Raw` byte position.

The fixed [`StringInput`](##Complexity.Program.StringInput) interfaces support
strings, arrays of strings and prefixes of other registered input fields.
Arrays use the existing shared row-boundary/payload layout, retaining empty
rows. `Input`/`RamInput` record deriving can therefore retain fields of type
`Array String` instead of asking authors to replace their mathematical inputs.
Output observations use the same layouts at the actual final heap.

The frontend accepts `text.length`/`String.length text`,
`text.toList.getD index fallback` and
`String.ofList (List.replicate length character)`. The character lookup fuses
the complete expression into the existing bounds check and code-point read;
it does not materialize an intermediate linked list or provide a standalone
`String.toList` conversion. Repetition invokes the real initialized allocator,
including at length zero. The empty literal `""` uses that zero-length allocation;
nonempty literals and arbitrary `String.ofList` are not yet supported.

`Array String.getD` reads the actual row boundaries and returns a borrowed view,
or the complete supplied String fallback out of bounds. All correspondence
proofs retain the actual heap and preserve prior string/array contents across
these reads and allocations, including aliases. Shape extension alone would
not justify preserving mutable contents.

The [String consumer](##Complexity.Examples.Strings) uses `program_correct`
to state ordinary equations for lookup, length, repeated construction and a
record containing string rows. Its `replicateBodyCost_linear` composes the
existing allocator certificate through the actual caller, counting initialized
cells and wrapper instructions. It is conditional on arena readiness, not a
complete `Program.TimeO` or native CPU-cost theorem. Word ranges and capacity
remain separate from source correctness.

General string mutation, mixed-character construction and deeper row access
remain open. In particular, a row whose payload itself has row boundaries
cannot be returned as canonical zero-based storage merely by slicing nonzero
inner offsets; it needs a justified borrowed representation or an actual,
charged rebasing operation.

## Linked-node storage

The List contracts here use `Representation.bufferList`: explicit mathematical
observations of array-backed operations, not the default source List
implementation. `Representation.list` instead observes actual linked-node
contents at the current heap. The selected List runtime
is an immutable linked-node representation with shared tails. Its source heap
now has separate immutable nodes, typed `cons`/`uncons` and a
`NodeRef.Contents` relation to ordinary Lean lists. Old contents survive buffer
writes and fresh allocations without requiring disjoint tails. The RAM heap
representation stores actual tail addresses, and the backward-link invariant
retains the complete chain during prefix reclamation. The checked
[allocation bridge](##Ram.LanguageCompiler.ArenaRep.cons_measured) connects the
actual cursor update and three stores to `head :: values`; the
[read bridge](##Ram.LanguageCompiler.HeapRep.list_cons_read) reads the same head
and shared tail while preserving all memory. The existing compiler gives these
blocks 21 and 13 instructions, respectively, excluding operand preparation,
outer option handling and call overhead. Typed references already pass through
effectful parameters, returns, products and options using actual placed
addresses. The typed `Stmt.readNode` statement now binds the actual head and
shared tail, with source proof rules and ordinary/allocation-aware measured
simulation. Its effectful syntax is `let (head, tail) ← ref.read`, after
matching the optional root. The typed `Stmt.consNode` statement likewise binds
one freshly allocated reference and has source rules and allocation-aware
measured simulation. It captures three operand fields before the allocator,
giving a proved 27-instruction block before its continuation. The supported
[native List operations](ComplexityDocs/Verification/Lists.html) use this same path;
the complete operation library remains open. Array and Vector retain
contiguous layouts. Reusing List theorems does not justify replacing linked
`cons` or `tail` with unmentioned array allocation or copying.

## Callable list operations

The callable [emptiness operation](##Complexity.Language.List.IsEmpty.body)
matches an optional node root and refines ordinary `List.isEmpty`, preserving
the entire heap. Its [execution bound](##Ram.LanguageCompiler.List.IsEmpty.execute_le)
describes the same actual halted invocation, including the compiler's branch,
return and outer-call overhead. The input representation and launch capacity
are explicit; loading the inputs is outside this boundary. Native let-call
bindings support `xs.isEmpty` and `List.isEmpty xs` for Nat/Bool Lists, using the
same tag-only operation. Generated mathematical correspondence retains its
unchanged heap; shared measured-call and structural-cost rules give the native
wrapper its complete RAM invocation bound. The reusable readiness certificate
needs no node read, head range or time-bound premise. It does not provide
arbitrary expression-call hoisting. The general allocator bridge
requires only an existing tail root; the stronger List contents requirement
belongs to its mathematical specialization, not to a runtime traversal.

The callable [decomposition operation](##Complexity.Language.List.Uncons.body)
matches the root and reads a present node once. Its
[correctness theorem](##Complexity.Language.List.Uncons.refines) gives the
ordinary result `xs.head?.map (fun head => (head, xs.tail))` through the existing
option, product and linked-list representations. The heap stays exactly the
same, and the returned tail is the original reference, not a copied suffix.
Its [RAM theorem](##Ram.LanguageCompiler.List.Uncons.execute_le) includes the
full invocation cost derived from the same implementation, including the empty
branch, option construction and call overhead. Its composable
[measured entry](##Ram.LanguageCompiler.List.Uncons.arenaMeasured) accepts an
ordinary represented list at the current heap and a word-range proof only for
its present head. It preserves the actual result, entire heap and cursor, with
no proposed time bound or physical heap representation needed for readiness.
The [launch-heap entry](##Ram.LanguageCompiler.List.Uncons.arenaMeasured_of_heapRep)
derives that range when a heap representation is already available. Existing
scalar-head and allocating callers reuse these observations directly; their
complete RAM launch conditions and independent cost bounds remain intact.
Native `xs.uncons` and `List.uncons xs` use the same operation, but do not
constitute a complete persistent List library.

The [named linked-list client](##Examples.Language.LinkedList) writes:

```lean
source_program Implementation where
  def uncons (root : Option (NodeRef Nat)) : Option (Nat × Option (NodeRef Nat)) := do
    match root with
    | none => return none
    | some ref =>
      let fields ← ref.read
      return some fields
```

Its generated body is definitionally `List.Uncons.body .nat`. The ordinary
List contract and refinement therefore reuse the public library theorems
directly; there is no second implementation induction or register proof.

The callable [constructor](##Complexity.Language.List.Cons.body) allocates one
node and shares the supplied tail. Its
[correctness theorem](##Complexity.Language.List.Cons.total) gives ordinary
`head :: values`, the exact fresh root and heap, and preservation of old lists.
Its [RAM theorem](##Ram.LanguageCompiler.List.Cons.execute_le) retains these
facts for the same halted invocation, the three-word cursor advance and the
full invocation bound. Operand preparation, initialization, optional-root
packaging and call/return/halt are included; input loading remains separate.
The named client writes:

```lean
source_program Construction where
  def cons (head : Nat) (tail : Option (NodeRef Nat)) : Option (NodeRef Nat) := do
    let ref ← NodeRef.cons head tail
    return some ref
```

Its body is definitionally `List.Cons.body .nat`, so the public correctness
contract applies directly. The singleton client writes `NodeRef.cons head none`
without a type annotation and derives ordinary `[head]` contents from the same
contract. Neither client supplies a register proof. Capacity and word ranges
remain separate conditions of the RAM execution, not of source correctness.

## Fold contracts and callbacks

The shared [linked fold](##Complexity.Language.List.Fold.body) runs a real
`while` traversal and invokes the selected source callback for every node.
Its [callable contract](##Complexity.Language.List.Fold.program_refines) relates
the result to ordinary `List.foldl`. The accumulator may use any existing
representation; it is not restricted to a natural number or a heap-free value.
The callback contract needs its domain only along the actual mathematical fold
trajectory. It may allocate or modify mutable buffers, while the original
immutable list stays observable in the final heap. Termination follows from the
represented list, independently of proposed instruction or arena budgets.
Its [RAM theorem](##Ram.LanguageCompiler.List.Fold.execute_le) retains the same
result, final heap and cursor. The bound includes actual callback calls, linear
link traversal and the outer invocation and halt. The traversal itself adds no
length-dependent call depth. Callback arena reservations are summed along the
mathematical trajectory; reusable scratch peaks are not yet separated from
retained growth by this interface. The represented native frontend selects this
same implementation for its supported pure and allocating native callbacks.

The [numerical interface](##Ram.LanguageCompiler.List.Fold.invocationBound_eq_sum)
turns callback charges into an ordinary `List.mapIdx` sum: each charge sees the
accumulator computed by folding the preceding `take` prefix. A
[constant callback budget](##Ram.LanguageCompiler.List.Fold.invocationBound_const)
gives an exact size-only affine formula. A varying budget needs the common
envelope only at [visited prefixes](##Ram.LanguageCompiler.List.Fold.invocationBound_le_linear).
The [linear asymptotic theorem](##Ram.LanguageCompiler.List.Fold.isBigO_linearInvocationBound)
uses mathlib `IsBigO`; clients need not expand compiler coefficients. It bounds
the proved invocation envelope, not input loading or arbitrary native Lean
execution, and does not supply missing word-range or capacity proofs.

Existing pure callback equations feed the same fold contract through
[the callback bridge](##Complexity.Language.List.Fold.Contract.of_pure_eval).
Its [exact evaluation rule](##Complexity.Language.List.Fold.eval_eq_pure_of_contents)
retains the original heap and returns the ordinary `List.foldl` value, conditional
on the actual linked input representation. This reuses the general correctness
proof rather than proving a second loop. Existing finite-word realization and
cost proofs transfer through the shared
[resource bridge](##Ram.LanguageCompiler.FunctionArenaResources.of_functionRealizable)
and [cost bridge](##Ram.LanguageCompiler.FunctionArenaCostBound.of_functionCostBound).
The [fold's callable bound](##Ram.LanguageCompiler.List.Fold.functionCostBound)
can then be imported by another source function; it includes body initialization,
while the caller separately accounts for its calls, return and outer halt.

## Native node-action specifications

The [node action rules](##Complexity.Language.NodeRef.consM_spec) use the same
`ExceptT`/`StateT` proof interface as buffers. Default `@[spec]` rules describe
actual node allocation and typed lookup; separate `consM_list_spec` and
`readM_list_spec` rules expose ordinary cons contents and a shared tail through
the same linked representation. They preserve the real heap effects, including
old lists sharing the tail. The read statement's generated observation reuses
`readM` and its native specification; construction similarly reuses `consM`.
These actions also underlie the
[native construction path](ComplexityDocs/Verification/Lists.html). They do not
by themselves supply a complete persistent container operation library.
-/
