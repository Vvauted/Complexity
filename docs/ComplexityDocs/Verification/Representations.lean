/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.LinkedList
import Examples.Language.ProgramCompiled
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
