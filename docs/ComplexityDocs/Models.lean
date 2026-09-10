/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

/-!
# Working with data

Use the Lean or mathlib object whose theorems express your intended property.
A representation predicate connects that object to the implementation's memory, so the
algorithm proof can use mathematical operations rather than repeated pointwise heap updates.

Representations describe observations, not bijections between whole heaps and values.
The same object may live at different addresses, and unrelated cells can contain other data.
The current implementations store words; a view as naturals or other values additionally
needs the appropriate encoding and arithmetic facts.

## Pass a typed reference to existing data

The source declaration `fn sum(xs : array)` gives the function one array parameter.
The parameter's `xs.base` and `xs.length` fields are word locals. A `call sum(xs)`
passes those two words through the existing calling convention; `xs[i]` denotes
the existing indexed word load. These are source operations, not calls to Lean's `List`.

The [array-sum implementation](##Complexity.Computability.Ram.Array.Sum) also contains:

```lean
fn sumPair(left : array, right : array) {
  let leftSum ← call sum(left);
  let rightSum ← call sum(right);
  return leftSum + rightSum;
}
```

Its generated Lean argument builder `sumFunctions.arguments.sumPair` accepts two
`Ram.ArrayRef w` values. A reference contains only `base : Word w` and `length : Word w`.
It is passed by value, not allocated as a descriptor in the heap. The assertion
`array.Rep heapLimit xs entry` combines an exact length equation with the existing
`Ram.Source.ArrayAt` predicate. The list `xs` belongs to the mathematical specification,
not to the runtime argument payload.

Array and word parameters also compose: the
[counter](##Complexity.Computability.Ram.Array.Count) declares `fn count(xs : array, target)`.
Its argument builder takes an `ArrayRef` followed by a word. The
[permutation client](##Examples.Ram.ArrayCount) uses its represented-array contract and
`List.Perm.count_eq`, without reopening the counter's loop or parameter registers.

The sum and pair contracts return ordinary modular list sums and preserve shared state.
Because both operations are read-only, the two references may overlap. Constructing a
reference does not establish its contents, range or ownership, and it does not load or
allocate memory. Typed local bindings and array-valued function returns carry descriptors
for existing data. The [slice function](##Examples.Ram.ArraySlice) returns a borrowed
`ArrayRef` that its caller passes to sum. Those borrowed operations do not allocate;
the arena primitive below is separate, and automatic loading of Lean lists is still missing. See
[array references](##Complexity.Computability.Ram.Array.Ref) for the representation rules.

Local descriptors can be constructed with `array(base, length)`, copied from another
array binding or borrowed with `subslice(xs, offset, count)`. Each local binding
executes two word assignments; it does not clone or allocate the referenced cells.
`subslice` starts from a bound handle, so bind constructed or nested handles first.
Immutable bindings protect their fields, not the shared heap cells; `let mut`
permits assigning the descriptor's `base` and `length`. Neither form supplies
ownership or runtime bounds checks. Array-valued calls use the function's declared
`: array` result and receive both descriptor fields through the same calling convention.

The [ordinary sum application](##Examples.Ram.ArraySum) has the form
`sum array heapLimit entry safe hstack : Nat`. Its data inputs are the reference,
heap boundary and preloaded state. The mathematical list is existentially described
inside the erased safety proof, not passed as another runtime argument. `sum_eq`
connects this executable value to the modular list sum; the
[graph client](##Examples.Ram.GraphDegree) uses that equation to prove `sum_eq_degree`
with ordinary mathlib facts and no loop or frame proof. Neither application loads
the represented array. Generated `apply` returns the declared `Word`, `ArrayRef` or `Unit`;
use `applyState` for that value and reusable source shared state, or `runTotal` for
machine state and steps. `TypedFunctionContract` keeps these typed values in mathematical
postconditions; the raw execution still records their actual word fields.

The [copy application](##Examples.Ram.ArrayCopyFunction) returns `Source.State 32`
by projecting the state from copy's actual `Unit`-valued `applyState`. `copy_contents`
states that `arrayContents` of its destination
equals the source list; `copy_spec` also retains the source array, the destination
frame and unchanged streams. The lists occur in erased proofs, while actual RAM
stores produce the destination. Both arrays must already be represented and disjoint.
`copyThenSum` feeds this returned state to the existing sum application, reusing its
representation. This host-level sequencing is not a single compiled RAM program;
returning shared state is separate from returning an array reference. This copy returns
`Unit` while retaining its stores and shared effects; slice instead returns two descriptor fields.

## Allocate an initialized object

The [arena runtime](##Complexity.Computability.Ram.Memory.Arena.Function) now
provides a real callable allocator. Address zero holds a shared cursor. The
allocator reads it, reserves the requested interval, writes each initial value,
then returns the base/length descriptor. Its body uses `14 * length + 14` RAM
instructions; the complete preloaded call, return and halt uses
`14 * length + 69`. The one-time session bootstrap is a separate three-instruction
store. Neither count includes an implicit input loader.

The [typed connection](##Complexity.Computability.Ram.Compiler.Language.Arena.Execution)
proves that this execution implements `Heap.alloc`: the new native-array object
has its complete initialized contents, and existing objects retain their
addresses and contents. `ArenaRep` includes the cursor and exact scalar ranges.
Capacity requires `next + length ≤ heapLimit < 2^w`; code and stack capacity
remain separate runner premises. Zero-length allocation is supported and still
returns a fresh source object identity.

The [inline typed connection](##Complexity.Computability.Ram.Compiler.Language.Arena.MeasuredAllocation)
uses the same allocator at five fresh local slots. Its two operand assignments
and actual initialization cost `14 * length + 18`; the returned descriptor and
extended heap are proved at that same endpoint. It adds no function-table entry
and preserves caller locals outside those slots.

Use the actual returned shared state for subsequent calls. Returning restores
caller registers, not old heap contents or an old cursor. Later allocator calls
preserve an existing view at its original address. Allocation alone is monotone;
explicit scratch scopes below add safe reuse. Ordinary aliasing writes can still
change array contents. Arbitrary `free` and GC are not provided, and reserved
extent is not peak reachable space.

The typed core includes `Stmt.alloc`. Its evaluator and budget-free correctness
rules retain that same initialized object; the native VCG rule exposes ordinary
Array contents, freshness and shape growth. The
[general measured simulation](##Complexity.Computability.Ram.Compiler.Language.Arena.MeasuredSimulation)
composes allocating bodies through loops and recursive calls. It retains the
actual final heap, extended placement and shared cursor, including across
caller-register restoration; no per-program register proof is required.

The [function/runner interface](##Complexity.Computability.Ram.Compiler.Language.Arena.ProgramExecution)
combines independent source correctness with allocation readiness and reaches
the actual halted invocation. Source correctness requires no proposed time
budget. The RAM guarantee still requires positive word width, exact scalar
ranges, rooted represented arguments and sufficient arena/code/stack capacity.
Its count includes the body's two private-flag initialization instructions and
the outer call/return/halt overhead; input preparation and the one-time bootstrap
remain separate. Without scratch scopes, capacity tracks cumulative cursor growth,
not peak live storage.
The checked [allocation consumer](##Examples.Language.Allocation) calls `make`
to allocate a result, allocates again, then reads the original if nonempty and
returns it. `retain_runUntil` retains the original `ArrayRef` contents and the
actual runner count, including empty output. Its named `Named.make` uses
`Buffer.alloc`; `named_make_spec` proves ordinary `Array.replicate` contents
with `mvcgen`, without source capacity or time premises. Mathematical ranges
and loop/recursion invariants remain author work, not automatically inferred
by the generic register/placement proofs. Allocation-aware resource transport
through imports, the full library, all Examples, the routine source-frame
consumer and the complete manual build are checked on 0v0.

## Reclaim scoped temporary storage

In a named source program, `with_scratch do ...` keeps temporary allocations
within a lexical scope. Allocate longer-lived output before entering the scope.
On a safe exit, old objects keep their **current** contents while new objects
are discarded. Returning from inside the block still returns from the enclosing
function, after cleanup. No copying, freezing or rollback is implicit.

Safety requires all surviving local and returned handles to refer to objects
that existed at scope entry. Current array cells are scalars, so they cannot
hide further handles. The source reports an escaping reference without freeing
its heap; the compiled success theorem covers proved-safe exits, not a runtime
escape scanner. See the [scope specification](##Complexity.Language.Verification)
for the correctness rules.

The [RAM scope primitive](##Complexity.Computability.Ram.Memory.Arena.Scope)
saves and restores the shared cursor using six instructions in total. It changes
metadata rather than clearing cells, allowing later allocation to reuse addresses.
The [compiled simulation](##Complexity.Computability.Ram.Compiler.Language.Arena.Simulation.Scope)
proves that this preserves retained objects and runs cleanup after early returns.

The [physical workspace interface](##Complexity.Computability.Ram.Compiler.Language.Arena.Memory)
bounds all actual accesses throughout a complete function invocation by
`heapLimit + (depth + 1) * frameSize`. This includes inputs, retained outputs,
scratch, metadata and call frames. Registers, code, I/O streams and host-side
loading/conversion are separate. The bound is a sufficient address envelope,
not an exact count of reachable live objects; a restored final cursor alone
would not bound intermediate workspace.

The [repeated scratch client](##Examples.Language.ScopeCompiled) uses the same
named source declaration for correctness and compiled execution. It allocates
one surviving result cell, repeatedly calls a worker with two nested length-`n`
scratch buffers, and returns that result. `make_runUntil` proves actual halt,
mathematical contents and a workspace envelope of
`entryCursor + 1 + 2*n + 2*frameSize`, independent of the repetition count.
Word ranges and representation/capacity conditions remain explicit. The
source loop's Lean well-founded proof supplies termination before resource
readiness is considered.

For scalar code, `source_program (pure)` supplies native total functions and
automatically proved source correspondence. The checked
[factorial](##Examples.Language.Factorial) theorem is ordinary
`Implementation.factorial n = Nat.factorial n`, using induction and one native
termination proof; Scalar and Remainder use the same interface. This pure subset
supports self-recursion and acyclic calls, not pure `while`, mutual recursion
or buffers. Buffer programs retain their mathematical effectful contracts;
neither interface identifies Lean runtime with certified RAM instruction cost.

## Fold through an expression or a proved function

Sum and count both use a scoped `for` with one expression update to a scalar
accumulator. The [expression function rule](##Complexity.Computability.Ram.Array.ForIn.Expression)
derives private slots from the generated body and return equations and proves an
ordinary `List.foldl` result. It accepts an array first, followed by word parameters,
and preserves the complete `array.args ++ captures` parameter prefix. Thus count's
target needs no separate preservation invariant. Clients still prove the actual
expression's read safety and evaluation equation, with those parameter equalities
available, and provide the represented array and non-wrapping address premises.
The mathematical fold identity then recovers the standard list sum or count.

The [array-fold sample](##Examples.Ram.ArrayFold) writes its traversal directly:

```lean
for x in xs {
  accumulator := call addSquare(accumulator, x);
}
```

The frontend lowers `for` to [ordinary source instructions](##Complexity.Computability.Ram.Source.ForIn).
It copies the array's base and length into two fresh private cursor locals, then
loads each element into a third local. The source binding `x` is immutable and
scoped to the body. Loop control does not advance the original array descriptor;
array contents are read on each visit, not copied into a snapshot.

`Ram.Source.Array.ForIn.function_contract` packages this single-array, scalar-accumulator,
fixed-helper shape as an ordinary `List.foldl`. Generated body and return equations
determine the slots and call target; the sample discharges the layout premise with `decide`.
The client supplies the actual helper's `FunctionContract`, lookup and array premises,
without constructing a register record or a separate list of call expressions.
The helper must return the mathematical step value and preserve shared state.
This [function-level rule](##Complexity.Computability.Ram.Array.ForIn.Function)
reuses cursor safety, termination and framing, with no time bound.

The sample reuses `sumSquares` from the same `LocalBindings.functions` declaration.
Each iteration calls `addSquare`, which calls
the existing `square`. Its contract and `eval_eq` theorem describe the returned word
as the encoded ordinary sum `(xs.map (fun x => x.toNat ^ 2)).sum` and preserve caller
state. `eval_toNat` recovers the exact natural-number result when that sum fits;
the general equation retains modular word arithmetic.

This call-based function rule covers the fixed-helper shape above. Together with
the expression rule it handles specific read-only scalar folds, not arbitrary
`for` bodies or automatic proofs of every source loop. Mathematical steps describe
actual expressions or calls, not free Lean callbacks. Represented input,
non-wrapping addresses and callee safety remain required. Richer bodies, multiple
accumulators, short-circuiting and mutable-fold contracts are not supplied by these
rules, even though ordinary functions can return array references. Automatic list loading
also remains outside these rules. The lower-level
[call-based fold](##Complexity.Computability.Ram.Array.Fold.Call) remains available
for explicitly configured cursor loops.

The mathematical traversal uses the ordinary
[list/state equation](##Complexity.Data.List.StateM) `List.forM_modify_run`:
repeated accumulator updates have the same final state as `List.foldl`.
It is generic in both element and state types and imports no RAM model.
The array proof separately establishes that actual loads and updates implement
this traversal; the pure equation supplies neither machine execution nor its cost.

## Choose what the proof needs to observe

| Mathematical view | Representation or observation | Useful properties |
| --- | --- | --- |
| `List (Word w)` | `Ram.ArrayRep` | Indexing, updates, order and permutation |
| `Array (Word w)` | View of `Ram.ArrayRep` | Native array indexing |
| `List.Vector (Word w) n` | View of `Ram.ArrayRep` | Fixed length |
| `ι → Word w` | `Ram.IndexedRep` | `Function.update`, reindexing and extensionality |
| `Multiset (Word w)` | `Ram.ArrayRep.multiset_eq` | Multiplicity without order |
| `Finset (Word w)` | `Ram.ArrayRep.toFinset_eq` | Membership without multiplicity |
| `Matrix (Fin m) (Fin n) (Word w)` | `Ram.MatrixRep` | Rows, columns and matrix updates |
| `Finmap (fun _ : κ => Word w)` | `Ram.FinmapRep` | Optional lookup, insertion and erasure |

For example, `Ram.ArrayRep.contents_eq` gives an ordinary observation equality. Rewrite with
it directly or use `ram_model [h.contents_eq, mathematical_facts]`. Vector views reuse
mathlib's `Equiv.vectorEquivFin`; matrices are mathlib matrices, not a parallel matrix type.

Choose a lossy observation only when it preserves what the specification needs. A set view
cannot prove permutation, and replacing one array entry does not remove the old value from
the set if another occurrence remains. The [multiset](##Complexity.Computability.Ram.Array.Multiset)
and [finite-set](##Complexity.Computability.Ram.Array.Finset) interfaces make this distinction
explicit.

## Apply an implemented operation

`Ram.ArrayRep` describes contiguous non-wrapping contents; `Ram.Source.ArrayAt` also records
that the cells lie below the source heap boundary. For a general address function, use
`Ram.IndexedRep` and `Ram.Source.IndexedAt`.

The [indexed contracts](##Complexity.Computability.Ram.Memory.Contracts) and
[array contracts](##Complexity.Computability.Ram.Array.Contracts) describe real loads,
stores and swaps. Apply them with `ram_total_apply`, keeping the operation body opaque.
The indexed contracts are budget-free; the tactic can also forget the cost of an existing
array contract. Their postconditions give the mathematical result and the concrete state
effects needed by later operations.

A store needs an injective address function: otherwise one physical cell could represent
several logical entries. A valid contiguous array supplies this fact from its no-wrap bound.
Runtime address expressions, index bounds and temporary-register requirements are still
part of the operation's precondition. A representation alone neither allocates memory nor
implements address computation.

For stateful models, the [indexed StateM bridge](##Complexity.Computability.Ram.Memory.StateM)
describes loads using `get` and stores using `modify (Function.update ...)`.
These refinements retain the endpoint needed to compose with other operations.

## Work on a slice and recover the whole object

Array `take`, `drop` and `slice` views borrow existing cells. After modifying a prefix,
`Ram.ArrayRep.replace_prefix` reconstructs the new prefix followed by the old suffix.
Split/reassembly rules retain the original full-allocation bound: two individually valid
views do not by themselves show that their union avoids wrapping.

For a typed reference, `Ram.ArrayRef.Rep.subslice` reuses these rules to describe
`(xs.drop offset).take length` at a contained borrowed interval. `ArrayRef.subslice`
constructs host-side metadata without copying cells. Inside a source function,
`let window : array := subslice(xs, offset, count);` instead executes the base-address
arithmetic and descriptor assignments. The [slice sample](##Examples.Ram.ArraySlice)
instead returns that borrowed reference from `slice` and passes it to the existing sum
function. It states the result using
ordinary list `drop` and `take`. Containment and non-wrapping premises remain explicit;
arithmetic, bindings and calls retain their execution costs. A mathematical slice
view does not silently perform any of those source instructions.

For a matrix row, use `Ram.Source.MatrixAt.row_array`, apply an array operation, then use
`Ram.Source.MatrixAt.replace_row_array` to recover the updated matrix. If the operation also
writes scratch memory, `Ram.Source.MatrixAt.replace_row_array_two` uses its two-buffer frame
and a disjoint scratch region. It does not claim that scratch contents were preserved.

The [matrix copy](##Complexity.Computability.Ram.Matrix.Copy) and
[matrix sorting](##Complexity.Computability.Ram.Matrix.MergeSort) modules illustrate this
workflow. Row sorting reuses the existing sorting call and its RAM refinement, then proves a
sorted permutation of that row and equality of the others with native stateful reasoning
and mathlib facts. It neither implements sorting again nor compiles `modify` automatically.

A transpose or submatrix is likewise a view of existing memory. Changing mathematical
coordinates does not physically transpose, copy or rearrange that memory. See
[array slices](##Complexity.Computability.Ram.Array.Slice),
[matrix representations](##Complexity.Computability.Ram.Matrix.Memory) and
[writeback](##Complexity.Computability.Ram.Matrix.Writeback) for the precise rules.

## Preserve an unrelated object

A frame theorem says which cells an operation leaves unchanged. The shared interface uses
ordinary `Set.EqOn` and disjointness, so different represented data structures can compose.
Array and two-buffer frames supply these effects for their existing operations.

A checked [typed-source rule](##Complexity.Language.Effects.Heap) derives
`Exec.heap_prefix` and `Exec.contents_frame` from `Stmt.NoCellWrites` for the
statement and every callee, even on finite faults. Contents transport uses
[`Buffer.Contents.mono_prefix`](##Complexity.Language.Heap.Prefix) and `List.IsPrefix`, allows fresh allocation initialization
and conservatively excludes explicit cell writes. This does not infer the
author's mathematical range, capacity or loop-invariant arguments. The allocation
consumer's `retained_frame` applies this shared rule.

`Ram.Source.Refines.frame_heap` lifts a model `f : α → β` to
`fun (x, z) => (f x, z)` when the other object's observed cells are disjoint from the proved
write region. `Ram.Source.Refines.stateM_frame_heap` gives the analogous product-state rule
without changing the original returned value. No separate ownership datatype is required.

When the parent object overlaps the updated subview, use a writeback theorem instead of a
disjoint frame: it combines the new contents on the selected indices with the old contents
elsewhere. [Indexed writeback](##Complexity.Computability.Ram.Memory.Indexed.Writeback)
expresses this with ordinary `Set.piecewise`.

These are endpoint claims. To show that cells remain unchanged throughout execution,
use the [actual write-footprint results](##Complexity.Computability.Ram.Execution.Memory)
described in [the backend chapter](##ComplexityDocs.Backend).

## Use a partial map when absence matters

`Ram.FinmapRep` is a direct-address representation over a bounded key universe.
Each key has a payload cell and a presence marker; consequently `none` and `some 0`
are different. The mathematical interface reuses mathlib's `Finmap.lookup`, `insert`,
`erase` and extensional equality.

Insertion writes the payload and marker; erasure clears the marker; lookup checks presence
before reading a payload. The [contracts](##Complexity.Computability.Ram.Memory.Finmap.Contracts)
and [lookup interface](##Complexity.Computability.Ram.Memory.Finmap.Lookup) expose those
actual operations. Their [StateM refinements](##Complexity.Computability.Ram.Memory.Finmap.StateM)
compose through native bind and reuse ordinary facts such as `Finmap.lookup_insert`.

This is not a sparse map or hash table. The reserved addresses must fit and be distinct,
and an empty representation requires already-zero presence markers. Allocation, marker
initialization and a computational key-to-address conversion are not supplied by the
representation predicate.

## Keep the model when compiling

Use `Ram.Source.Refines.compile_observed` to export a represented result to the halted
target state, or `Ram.Source.Refines.compile_observed_with_timeBound` for a timed result.
The observation bridges `Ram.Source.State.Observes.array`,
`Ram.Source.State.Observes.indexed`, `Ram.Source.State.Observes.matrix` and
`Ram.Source.State.Observes.finmap` cover the existing representations.

For a preloaded heap, `Ram.Source.RelContract.compile_block_observed` starts from an explicit
matching target state. The theorem retains source-visible observations, not equality with
the target's private stack. See
[execution export](##Complexity.Computability.Ram.Verification.Execution) for the entry-state
and capacity premises.
-/
