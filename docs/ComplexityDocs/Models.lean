/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

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
allocate memory. General array-valued local bindings, returned array values and automatic
loading of Lean lists are not supplied by this parameter syntax. See
[array references](##Complexity.Computability.Ram.Array.Ref) for the representation rules.

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
constructs metadata; it does not copy cells or itself implement in-program pointer
arithmetic. Expressions used by an actual source call are evaluated and charged by the
call compiler.

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
