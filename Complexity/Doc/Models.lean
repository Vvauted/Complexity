/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Data models and memory

Choose the ordinary Lean or mathlib object whose existing theorems express the intended
property. Representations connect that object to memory; clients need not reduce all
reasoning to lists or repeated pointwise register calculations.

An entire heap is usually not in bijection with a mathematical object: addresses, unused
cells and unrelated objects can vary. Representation predicates and observation equalities
express the connection without imposing such a bijection.

## Choosing a model

| Mathematical object | Observation bridge | Real update described by |
| --- | --- | --- |
| `List (Word w)` | `ArrayRep.contents_eq` | `List.set` |
| `ι → Word w` | `IndexedRep.contents_eq` | `Function.update` |
| `Array (Word w)` | `ArrayRep.toArray_contents_eq` | `Array.set` |
| `List.Vector (Word w) n` | `ArrayRep.vector_contents_eq` | Indexed update |
| `Multiset (Word w)` | `ArrayRep.multiset_eq` | Erase one old occurrence, then add the new value |
| `Finset (Word w)` or `Set (Word w)` | `ArrayRep.toFinset_eq` | Occurrence-aware replacement |
| `Matrix (Fin m) (Fin n) (Word w)` | `MatrixRep.contents_eq` | One-entry row update |
| `Finmap (fun _ : κ => Word w)` | `FinmapRep.contents_eq` | `Finmap.insert` and `Finmap.erase` |

The implementations use words. Interpreting entries as naturals, integers or other numeric
objects requires the appropriate encoding and arithmetic theorems; a mathematical view does
not alter the runtime datatype.

Once an observation equality is available, rewrite it normally or use
`ram_model [h.contents_eq, mathematical_facts]`. This works for arbitrary model types.
For example, `ArrayRep.multiset_eq_iff_perm` identifies multiset equality with list
permutation, while `card_toFinset_eq_length_iff` characterizes distinctness by `List.Nodup`.
Finite-set equality alone loses order and multiplicity. A finite-set replacement inserts
the new value and removes the old one only if no occurrence remains. Vector views reuse
mathlib's existing `Equiv.vectorEquivFin` instead of introducing another vector type.

## Indexed layouts and actual updates

`Ram.IndexedRep` describes values at selected addresses. `Ram.Source.IndexedAt` also bounds
those addresses by the source heap boundary. Neither asserts exclusive ownership or performs
allocation. `reindex` is ordinary composition and can restrict or repeat indices. Recovering
the original representation from a reindexed one requires surjectivity; an equivalence
supplies it.

The store theorem requires an injective address function. Without that premise, one physical
store might change several logical entries. A contiguous array derives injectivity from its
no-wrap bound. `store_outside` and `setMem_outside` preserve a model when the changed address
is outside its image.

`Ram.Source.Indexed.read_contract` and `Ram.Source.Indexed.store_contract` package actual
load/store instructions as budget-free relational contracts. Apply them with
`ram_total_apply`; their results retain the mathematical value or update, the exact concrete
endpoint and, for a store, equality outside the written cell. Safe expression evaluation and
the actual operand equations remain implementation premises.

The corresponding `read_stateM` and `store_stateM` describe native `get`/`pure` and
`modify (Function.update ...)`. They retain the exact `entry.setReg` or `entry.setMem`
endpoint, so later composition does not lose unrelated register or I/O facts.

## Arrays, slices and pointers

`Ram.ArrayRep` relates a contiguous non-wrapping allocation to a list.
`Ram.Source.ArrayAt` adds heap bounds; `ArrayFrame` describes which surrounding memory is
unchanged. `ArraysDisjoint` proves interval separation. Existing read, store and swap
contracts are in `Ram.Array.Contracts`; swap permits equal indices but records its actual
temporary-register freshness requirement.

`take`, `drop` and `slice` borrow standard list views at the appropriate address offsets.
`split` exposes two adjacent views; `reassemble` combines their new contents using the
original full-allocation bound. Two individually valid views do not by themselves prove
that their union avoids wrapping.

After modifying a prefix, `replace_prefix` reconstructs the new prefix followed by the old
suffix. `ArrayFrame.within` enlarges a slice's frame to the containing allocation.
`ArrayAt.exists_contents` observes the current contents of a scratch extent while retaining
its existing bounds; it neither allocates nor initializes that memory.

For an address computed at runtime, `ArrayRep.exists_index_iff` identifies represented
addresses with the natural half-open interval. `ArraysDisjoint.addr_ne` excludes aliasing
of valid elements. `ArrayAt.store_at` combines interval membership and an exact single-store
effect into address safety, a `List.set` result and its memory frame.

The reusable copy, lower-bound search, insertion, merge and sorting modules consume these
interfaces. Lower bound reuses ordinary `List.findIdx` properties; sorting uses `List.Perm`,
`List.Pairwise` and the canonical sorted list. A mathematical `List.insertionSort` in a
specification does not determine the executed algorithm: the recursive merge-sort
implementation still performs real recursive calls, merge and copy-back.

## Preserving other objects

`IndexedAt.frame` consumes ordinary `Set.EqOn finish.mem entry.mem writesᶜ` and disjointness
of the observed address range from the proved write set. `ArrayFrame.eqOn` and
`TwoBufferFrame.eqOn` supply these effects for existing array operations. Matrix and indexed
objects can therefore survive an unrelated array operation without another entry-by-entry
execution proof.

`TotalRelContract.frame_heap` preserves an arbitrary heap predicate after proving that it
depends only on the specified cells. `Refines.frame_heap` lifts a model `f : α → β` to
`fun (x, z) => (f x, z)` while retaining another mathematical object. Footprints may depend
on the represented input. These rules use ordinary sets and products, not a new ownership
or workspace datatype.

`Refines.stateM_frame_heap` provides the native stateful form on `σ × γ`. It returns the
original computation's value and updated `σ`, with `γ` unchanged. The resulting state/result
shape already composes through native bind. `stateM_equiv` uses mathlib's `StateT.equiv`
and ordinary equivalences to present a product as a record or change other mathematical
coordinates. Such a model conversion is not a physical memory-layout conversion.

These frame rules describe endpoints. To prove that cells remain unchanged at every actual
intermediate step, use the execution-footprint interfaces described in
[the backend chapter](##Complexity.Doc.Backend).

## Matrices and overlapping views

`Ram.MatrixRep` gives a row-major layout using mathlib's `finProdFinEquiv` and a
full-allocation no-wrap bound. `MatrixAt` also retains heap bounds. Rows, columns, transposes
and submatrices are views of the same memory. A transpose view neither physically transposes
the allocation nor establishes a new row-major layout.

`Ram.Source.Matrix.read_stateM`, `store_stateM` and `store_col_stateM` reuse the generic
indexed operations. Reads use the ordinary currying equivalence. Both store forms update
one entry; one uses `Matrix.updateRow`, the other `Matrix.updateCol`. Their equivalence is
the mathematical lemma `Matrix.updateCol_update`, not a second machine implementation.
No fresh injectivity proof is needed from a client of a valid matrix representation.

When a subview is changed, its parent overlaps the write footprint. Use
`IndexedRep.replace_on`, which combines the new observation on a selected index set with
the old observation outside it, producing standard `Set.piecewise`. Address injectivity
ensures that writing the selected view cannot alias another index.

`MatrixRep.replace_row` and `replace_col` yield native matrix updates. `MatrixAt.row_array`
borrows a contiguous row as `List.ofFn (A i)`; `replace_row_array` recovers the parent matrix
from an array operation's result and frame. `Ram.Source.Matrix.copy_row_stateM` is a concrete
consumer: it uses the existing array-copy loop with native model
`modify (fun A => A.updateRow i values)`. It retains the whole copy postcondition, including
source contents, final pointers, I/O and the memory frame.

Scratch-aware operations require a larger write footprint. `IndexedRep.replace_on_union`
allows changes in the selected view and an auxiliary region. `MatrixAt.replace_row_array_two`
uses an actual two-buffer frame and scratch disjoint from the matrix; it does not incorrectly
claim that scratch remained unchanged.

The merge-sort model can be restricted to fixed-length vectors with `stateM_subtype`, using
the proved length invariant. `Equiv.vectorEquivFin` then exposes a finite-function state.
The same fixed sorting call implements `Ram.Source.Matrix.sort_row_stateM`; its native
model modifies one row using `Array.MergeSort.sortedFin`. `sort_row_spec` proves a sorted
permutation of that row and equality of all other rows with `mvcgen` and mathlib facts.
Scratch observations, I/O and caller-register restoration remain in the refinement.

## Partial maps

`Ram.FinmapRep` represents a partial map over a bounded direct-address key universe.
Each key has a payload cell and a presence marker: zero means absent, nonzero means present.
Thus `none` and `some 0` are distinct. Absent payload cells are unconstrained.

The interface reuses mathlib's `Finmap.lookup`, `insert`, `erase`, domain theorems and
extensional equality. `FinmapAt` retains bounds on reserved cells. An empty representation
requires already-zero markers; there is no free initialization. This is not a sparse map or
hash table, and an injective layout into finite word addresses cannot cover an infinite key
universe. Zero-default functions are not interchangeable with partial maps when presence
of a stored zero matters.

`Ram.Source.Finmap.insert_contract` implements payload and marker stores;
`erase_contract` clears the marker. Lookup tests presence and conditionally reads payload,
returning an ordinary optional value. Its contracts retain the exact endpoint and relevant
frames. The runtime address operands, nonzero insertion marker and required register
distinctions belong to the implementation's preconditions.

Native insert, erase and lookup refinements compose through `stateM_bind`. The actual
`insert_lookup_stateM` uses the ordinary mathematical computation:

```lean
do
  modify (fun map => map.insert key value)
  let map ← get
  pure (map.lookup key)
```

Its native proof reuses `Finmap.lookup_insert`, and the resulting `some value` fact remains
available in the output representation. `insert_lookup_stateM_frame` preserves another
localized heap model; `insert_lookup_stateM_indexed` specializes it to indexed objects.
Only the two actually changed cells must be disjoint from the preserved view, not the entire
reserved map region.

## Exporting represented results

`Refines.compile_observed` transfers any output model to the same halted target execution,
using a proved transport along `Source.State.Observes`. Existing `Observes.array`, `indexed`,
`matrix` and `finmap` supply concrete observation bridges. The variant
`compile_observed_with_timeBound` also includes a separately proved time bound.

For a preloaded heap algorithm, `RelContract.compile_block_observed` starts from an explicit
matching block-entry state and counts the real final halt. `Observes.arrayFrame` and
`twoBufferFrame` retain source-visible memory frames without equating private compiler-stack
memory with the source heap. The entry state, code fit and sufficient stack capacity must
match the theorem being used.
-/
