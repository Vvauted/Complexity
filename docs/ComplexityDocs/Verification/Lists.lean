/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.LinkedList
import Examples.Language.LinkedListAllocation
import Examples.Language.LinkedListCompiled
import Examples.Language.LinkedListComposition
import Examples.Language.LinkedListFoldAllocation
import Examples.Language.LinkedListViewsCompiled

/-!
# Proving linked-list programs

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Write a list program

The [represented frontend](##Complexity.Language.Syntax.Represented)
accepts ordinary `List Nat` arguments and generates both a mathematical
function and a node-backed source function. The
[linked-list consumer](##Examples.Language.LinkedList) proves, for example,
`Native.sumFrom values initial = initial + values.sum` using existing List
algebra. Its generated `Native.sumFrom_refines` establishes the implementation
correspondence; `Refines.of_math` combines it with the mathematical theorem.
Constant initial values, reordered parameters, immutable locals, consecutive
fold calls and calls to earlier native declarations use the same construction.
Input lists may share tails. Native cons allocation and List-valued results use
the same represented-function interface. List accumulators and allocating
callbacks from completed native families are supported too. The examples here
retain the `(native)` compatibility naming. Represented self-recursion has a
checked source correspondence; mutual recursion, dynamic callbacks and general
element layouts remain unfinished;
the underlying effectful fold contract retains its wider scope.

Declare the actual pure callback, then use it in an ordinary-looking native block:

```lean
source_program (pure) Reducer where
  def add (accumulator : Nat) (head : Nat) : Nat := do
    return accumulator + head

source_program (native) Native importing Reducer where
  def sumFrom (values : List Nat) (initial : Nat) : Nat := do
    let result := values.foldl Reducer.add initial
    return result
```

Ordinary `let :=`, fully qualified `List.foldl`, named-list method calls and
earlier same-family function calls select the same checked operation path.
The generated source still traverses actual links and invokes the selected
source callback; Lean's mathematical `List.foldl` is not a RAM primitive.

List construction can also be written at its mathematical type:

```lean
source_program (native) NativeConstruction where
  def prepend (head : Nat) (values : List Nat) : List Nat := do
    let result := head :: values
    return result
```

The generated mathematical equation is
`NativeConstruction.prepend head values = head :: values`. The implementation
calls the actual allocating constructor and shares the supplied tail. Its
`_action_rel_native` observes the returned root in the real final heap and
preserves every previously represented list. `_refines` then combines with
ordinary mathematical proofs in the same way as the read-only example.
`List.cons`, explicitly typed empty lists, successive list-returning calls and
folds of both old and new lists are exercised by the existing linked-list
consumer. Allocation is not an unchanged-heap action, a runtime decoder or a
free mathematical operation. The traversal operation library and general
element layouts are still incomplete.

## Branches and matching

An explicitly typed conditional can return a list to a common continuation:

```lean
source_program (native) NativeBranches importing NativeConstruction, Reducer where
  def chooseSum (flag : Bool) (head : Nat) (left : List Nat) (right : List Nat) : Nat := do
    let chosen : List Nat ← if flag then do
      let selected := head :: left
      return selected
    else do
      let selected := NativeConstruction.prepend head right
      return selected
    let result := chosen.foldl Reducer.add 0
    return result
```

The checked consumer proves the ordinary equation
`NativeBranches.chooseSum flag head left right = head + (if flag then left.sum else right.sum)`.
Generated correspondence follows the actual selected branch's allocation and
returned root, preserves both old lists, and then composes the fold at that
branch's final heap. The author needs no intermediate-heap proof. The `:= if`
form uses the same lowering; this fragment requires an explicit supported result type
and returning branch blocks. General native patterns and mutually recursive
families remain separate work. The local result slot and its copies are real source operations,
not uncharged mathematical selection.

List matching uses the same result-binding interface:

```lean
source_program (native) NativeViews importing NativeConstruction where
  def replaceHead (replacement : Nat) (values : List Nat) : List Nat := do
    let tail : List Nat ← match values with
      | [] => do
        return ([] : List Nat)
      | _head :: rest => do
        return rest
    let result := NativeConstruction.prepend replacement tail
    return result

theorem replaceHead_eq (replacement : Nat) (values : List Nat) :
    NativeViews.replaceHead replacement values = replacement :: values.tail := by
  cases values <;> rfl
```

The compiler selects the real Uncons operation, matches its optional result and
projects the actual head/shared-tail pair. Neither mathematical List decoding
nor suffix copying is inserted. The generated correspondence transports the
ordinary equation to the actual source result and retains the original list.
There is no time or capacity premise in this correctness proof.

Option matching supports `none` and `some payload` in the same form. Products
and options may recursively contain lists as parameters and results; their
projections and heap-indexed observations compose through allocation. The
existing `inspectAndPrepend` consumer retains the old optional head/tail and
returns a new list together. Conditional and match result bindings now also
support scalars and recursive products/options containing Lists. Matching still
requires exactly two branches, returning do-blocks and an explicit result type.
`headOr` and `inspectOrPrepend` have checked source correctness, generated
correspondence and the end-to-end RAM theorems described below. `headOption`
still has only source correctness and generated correspondence.
Initialization and payload copies remain real source operations; bare node and
buffer slots and general patterns remain outside this fragment. Heap preservation
is composed only from proved-stable representations.

## Allocating callbacks

A fold callback can itself construct a list. Declare that native family before
the family that imports it:

```lean
source_program (native) ListReducer where
  def push (accumulator : List Nat) (head : Nat) : List Nat := do
    let result := head :: accumulator
    return result

source_program (native) NativeLists importing ListReducer where
  def reverseAppend (values : List Nat) (tail : List Nat) : List Nat := do
    let result := values.foldl ListReducer.push tail
    return result

theorem reverseAppend_eq (values tail : List Nat) :
    NativeLists.reverseAppend values tail = values.reverse ++ tail := by
  change values.foldl (fun accumulator head => head :: accumulator) tail = _
  exact List.foldl_flip_cons_eq_append'
```

The generated correspondence reuses the callback's real source execution and
the existing fold contract. It follows the newly allocated accumulator through
the actual heaps, while keeping the original input and shared tail observable.
No second traversal induction, heap decoder or resource budget is needed for
this correctness theorem. The existing consumer also calls native functions
across families and folds a newly returned reversed list to compute its sum.
These are statically selected source calls, not dynamic closures or uncharged
host List operations.

## Connect the same program to RAM

The [allocating compiled consumer](##Examples.Language.LinkedListAllocation)
proves `prepend_execute` for this generated wrapper's actual halted RAM run.
It retains the exact fresh root and heap, the old tail's contents and an arena
cursor increase of three words. Its exact count includes the imported cons call,
the wrapper's own initialization and return, and outer call/return/halt.
The launch retains finite-word, rootedness and code/stack conditions; the
additional arena capacity does not depend on tail length. This theorem does not
include input loading or infer resource bounds for an arbitrary allocating block.

The same consumer's `prependPair_execute` composes two actual calls to the
generated `prepend`, preserving the first call's heap and allocation cursor.
It proves the ordinary two-element extension, retained shared tail, an exact
six-word cursor increase and complete invocation count. The shared
[exact call rule](##Ram.LanguageCompiler.ArenaExecutionCost.call_measuredOfEq)
composes measured executions; its
[contract-based counterpart](##Ram.LanguageCompiler.FunctionArenaResources.call_measuredOfEq)
consumes independent correctness, allocation and cost contracts. Both retain
actual returned values and heaps for the continuation. Sequential calls reuse
the same caller depth; only a nested call adds a frame.

`choosePrepend_execute` connects the conditional construction consumer to RAM:
its true path allocates three nodes (nine words), while its false path allocates
two (six words). Both return to the same later call, preserve both original lists,
and retain the actual final heap. The exact instruction count includes only the
selected branch, result-slot initialization and copies, the common continuation,
and outer invocation overhead. The shared structural pass handles assignment,
sequencing and conditional execution as well as calls; it derives the option-tag
range from the launch's positive word width. The author still supplies callee
resource facts and sufficient space for the selected path.

`replaceHead_execute_le` covers the List-match program above through the same
halted RAM invocation. It returns `replacement :: values.tail`, preserves the
old list and advances the cursor by exactly three words. Its length-independent
instruction bound includes the real root test, possible node read, payload/join
copies, subsequent constructor and outer invocation. The shared pass handles
both actual Option paths and inherits payload ranges from the read's readiness
certificate; no manual raw-option split is needed in the connection proof.
Input loading is excluded, and finite-word/code/stack/arena conditions remain
explicit. The [structural arena cost pass](##Complexity.Computability.Ram.Compiler.Language.Arena.CostTactic)
now infers `replaceHeadCost` from the actual body and two supplied callee
certificates. Its [statement bound](##Ram.LanguageCompiler.StmtArenaCostBound)
applies to the same measured execution, without a handwritten call-table or
field-count formula. The inferred `prependCost` and `prependPairCost` likewise
replace the two straight-line wrappers' formulas; their exact ready/execution
equalities remain proved, not inferred from an upper-bound certificate alone.
Actual callee readiness, certificate selection, ranges and capacity remain
explicit. For input-dependent calls, the pass also accepts a supplied mathematical
index with `certificate at index via embedding`. The
[indexed call rules](##Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call)
check that index's actual arguments and precondition; they do not decode a List
from its raw root or guess a callee price. With
`certificate at index using specification via embedding`, an existing
`FunctionTotal` postcondition is available at the actual returned value and heap.
Later calls may use that relation to select their mathematical input index. The
structural pass still infers a fixed envelope for the current invocation; the
[general rule](##Ram.LanguageCompiler.StmtArenaCostBound.call_at_of_spec_le) also
accepts a result-dependent continuation budget and its mathematical combining
inequality, without asking the author to bound impossible callee outcomes.

The [arena loop cost rule](##Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Loop)
accepts a ghost index, invariant and potential over actual source states. It
retains changing heaps and cursor endpoints and includes false-exit and early-return
costs. It bounds an already supplied finite execution; it does not establish
termination or automatically discover the potential.

The [shared publication rule](##Ram.LanguageCompiler.ArenaMeasured.execute_le)
combines a measured body and its structural bound with an independent
`FunctionTotal` specification. It retains the same actual result, heap and cursor
and adds initialization, outer call and halt once. The mathematical specification
does not acquire a time-budget premise or select a different execution.

When the measured body supplies an exact count, use
[`ArenaMeasured.execute_eq`](##Ram.LanguageCompiler.ArenaMeasured.execute_eq)
instead. It publishes the same independent specification and retained observations,
with exact body and whole-invocation counts. `prependPair_execute` and
`choosePrepend_execute` use this interface without unpacking execution witnesses;
the branch-dependent cost still follows the branch actually taken.

The [typed-join RAM consumer](##Examples.Language.LinkedListViewsCompiled) uses
this rule for both scalar and compound results. `headOr_execute_le` returns
`values.head?.getD fallback` and leaves the heap and cursor unchanged.
`inspectOrPrepend_execute_le` returns its represented optional head/tail and List
together, retains the original List, and advances the cursor by three words only
on the true path. The false path has no cursor growth. Both have uniform full
invocation bounds including actual join initialization and field copies, not
exact branch-dependent instruction counts. Real launch and selected-path capacity
conditions remain explicit; input loading is outside this boundary.

The [allocating-fold consumer](##Examples.Language.LinkedListFoldAllocation)
proves `reverseAppend_execute` for the actual generated wrapper above, not just
for an independently invoked fold. It connects the ordinary reverse/append
equation to the returned list in the final RAM heap, while preserving both input
lists. The existing fold resource contract consumes the actual cons callback's
three-word allowance and compiler-derived constant instruction cost. The complete
wrapper has an affine invocation bound, a sufficient internal call depth of
three, and final cursor at most the initial cursor plus `3 * values.length`.
The count includes callback and wrapper initialization, calls, returns and halt.
Word, code/stack and arena conditions remain explicit; input loading is separate.
The cursor bound is not an exact peak-live-space claim.

Its `pushCost` and length-indexed `reverseAppendCost` infer callback and wrapper
costs from their actual bodies and existing callee certificates. The
[fold cost-only certificate](##Ram.LanguageCompiler.List.Fold.functionCostBound_of_actual)
uses the shared arena loop rule and the source iteration's existing correctness
postcondition. It requires mathematical admissibility, accumulator representation
and List contents, but not a second ready execution, a resource contract, word
ranges or spare capacity. The old callable bound delegates to this proof with its
stronger precondition. Constructing the actual ready execution still requires the
original range and capacity proofs; the cost-only rule does not remove them.
Use [`FunctionArenaCostBound.mono`](##Ram.LanguageCompiler.FunctionArenaCostBound.mono)
to strengthen a certificate's precondition and enlarge its bound: prove that the
new precondition implies the old one and that the old bound is at most the new
bound under that precondition. For the same program, body, arguments, word width,
heap limit and depth, the rule retains the actual execution, readiness and cost
internally. The two length-indexed fold certificates use this interface; budget
comparisons remain mathematical obligations, while capacity is still required
to construct a ready execution.

Conversely, [fold readiness](##Ram.LanguageCompiler.List.Fold.ready) and its
[callable resource certificate](##Ram.LanguageCompiler.List.Fold.functionResources_of_ready)
need no callback time bound. They reuse the independently proved finite source
loop through [indexed loop lifting](##Ram.LanguageCompiler.ArenaReady.while_of_exec_indexed).
The invariant tracks the actual cursor and remaining callback reservations;
real guard/body endpoints and immutable shared-tail observations pass between
rounds. The fold does not repeat its list or termination induction in the
resource proof. Its
[resource-only measured entry](##Ram.LanguageCompiler.List.Fold.arenaMeasured_of_ready)
packages that same execution and actual count without a proposed time bound.
The older bounded measured interface applies the independent cost certificate
afterward. The native read-only
[realization entry](##Ram.LanguageCompiler.List.Fold.Native.realizable_of_resources)
also needs no time bound; the existing scalar sum consumer uses it, while its
separate cost proof still supplies the callback's instruction bound. Range and capacity arguments
remain necessary, and the reservation is not an exact peak-live-space bound.

The [allocation-then-traversal consumer](##Examples.Language.LinkedListComposition)
connects the existing `NativeLists.reverseSum` to RAM. It allocates the actual
reversed List, then traverses that returned root with the original addition
callback. The cost proof supplies the first call's generated refinement with
`using`; the second call receives the new List observation at its actual heap.
The shared `linearFunctionBound` specializes both constant-callback folds, and
`reverseSumCost` infers their enclosing wrapper cost. The complete invocation
envelope is proved affine and `O(length)` in mathlib's `IsBigO`. The RAM result
returns `values.sum`, preserves the original List observation and bounds cursor
growth by `3 * values.length`; the second fold needs no new storage. A final-sum
bound supplies all finite-word addition ranges. Call depth five suffices,
independently of length. Both traversals, calls, initialization, returns and halt
are included; input loading and reclamation are not. Source correctness remains
the existing ordinary mathematical equation, with no time-budget premise.

## Compose resource certificates

The correctness proof needs only the mathematical List equation. The
[structural arena tactics](##Complexity.Computability.Ram.Compiler.Language.Arena.Tactic) now generate
argument selection, import transport and operational return continuations from
the actual source body. Their
[measured proposition](##Ram.LanguageCompiler.ArenaMeasured) packages the existing
execution, readiness and compiler count; it adds no evaluator or cost model.
For example, the two-constructor proof consumes its existing exact callee costs:

```lean
ram_source_arena_step
ram_source_arena_call exact using secondCost
ram_source_arena_call exact using firstCost
```

The constructor wrappers themselves use `exact using originalCost via embedding`;
they do not hide hand-written argument environments below this short proof.
For a known returned control, the pass also removes the existential packaging of
that actual value. Remaining cursor and cost comparisons stay mathematical goals;
it does not guess a result or unfold arbitrary cost definitions to close them.
The fold wrapper gets its actual execution and cursor bound from the
[composable fold entry](##Ram.LanguageCompiler.List.Fold.arenaMeasured_of_ready).
It supplies mathematical accumulator/list observations, callback correctness
and resources, admissibility, word ranges and remaining capacity. The shared
entry constructs the internal source arguments and reuses the existing traversal
proof; the caller does not assemble a resource-index tuple or another wrapper
totality/resource/cost contract. `reverseAppend` and `reverseSum` use this entry
without callback time certificates; those remain in their independent cost
proofs and bound the same execution. Its measured certificate is composed directly:

```lean
ram_source_arena_call measured using folded
  via NativeLists.Source.imports.NativeLists.Operations.fold0.embedding
```

The [measured call rules](##Ram.LanguageCompiler.ArenaMeasured.call_measured) retain
the same final state, returned value, cursor, core count and supplied observations.
Use [with_spec](##Ram.LanguageCompiler.ArenaMeasured.with_spec) to attach an
independent source postcondition before composing a call. The existing
`reverseSum` proof uses this to pass the new List observation from reverse to the
next fold, without unpacking or rebuilding `Exec`, `ArenaReady` or cost witnesses.
The final publication rule consumes the resulting measured proof directly.

When a later certificate depends on the actual return, name the continuation
before structural reasoning splits its branches:

```lean
ram_source_arena_call measured using read
  as finish parts cursor steps observed fits via embedding
```

This introduces the actual state, value, cursor, core count, supplied observations
and value-range proof, but does not execute the continuation proof pass.
Prepare the next callee certificate from these facts, then resume with
`ram_source_arena_step`. The `replaceHead` consumer uses this to prepare its
actual-tail constructor once before the empty/nonempty branches. Omitting `as`
keeps the existing automatic continuation behavior; genuine argument-range
obligations are never discarded.

The generic form `ram_source_arena_call (index := x) using total, resources, bounded`
is also available for independently specified indexed callees. All forms retain
the actual returned value, heap and allocation cursor. The contract form exposes
the actual count and its proved bound for the continuation. Compound exact-cost
or final-bound proof terms use parentheses before `via`. These checked consumers
do not establish automatic resource inference for arbitrary loops or recursive
native declarations; further operation-adapter selection remains open.

The [compiled consumer](##Examples.Language.LinkedListCompiled) proves
`sumFrom_execute` for this actual wrapper, including both internal call levels
and its outer invocation and halt. The condition
`initial + values.sum < 2 ^ w` bounds the actual intermediate sums; source
correctness itself needs no word-range or instruction budget. The launch retains
the represented inputs and code/stack capacity, and input loading remains
outside this preloaded-call bound. The resource proof reuses the original
callback and fold contracts. The ordinary-parameter
[fold resource interface](##Ram.LanguageCompiler.List.Fold.Native) supplies the
argument environments, represented input indices and zero-growth conversion;
the author supplies the mathematical range and callback resource facts.
This is not yet automatic resource inference for native declarations.
-/
