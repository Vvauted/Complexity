/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

/-!
# Proving correctness

Start with the mathematical result you want, then connect it to the implementation.
The correctness interface includes safety and termination, but asks for no time budget.
A separate [complexity proof](##ComplexityDocs.Complexity) can reuse the same invariants.

## Independent source proofs

The new [typed core](##Complexity.Language.Basic) has its own
[finite execution semantics](##Complexity.Language.Semantics), independent of RAM.
`Complexity.Language.TotalWP` has separate normal-continuation and return
postconditions; faults cannot satisfy it. `FunctionTotal` requires an actual
returned value, with no proposed instruction bound. See the
[source verification rules](##Complexity.Language.Verification).

The [named frontend](##Complexity.Language.Syntax) accepts scalar programs such as:

```lean
source_program (pure) Bounded where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if next ≤ limit then
      result := next
    else
      result := limit
    return result
```

It generates typed source bodies and executable curried Lean functions from the
same declaration. `Bounded.boundedIncrement n limit` has type `Nat`; its result
statement is the ordinary equality
`Bounded.boundedIncrement n limit = min (n + 1) limit`.
The generated `f_action` retains the independent source observation, and
`f_action_eq` exposes one source body in `ExceptT Fault (StateT Heap Part)` notation.
`f_action_eq_pure` proves that action equals `pure` of the native result for every
initial heap; `f_total` supplies the corresponding total source contract.
There is no second user-written implementation or manual heap conversion.
The pure fragment supports Nat, Bool, Unit and their recursively nested products
and options, finite-range `for`, self-recursion and acyclic calls,
but not buffers, general `while` or mutually recursive pure families.
The [iterative factorial](##Examples.Language.Factorial) uses one range and a
mutable accumulator. Its ordinary equality with `Nat.factorial` follows from
fold/product identities; generated source correspondence supplies totality
without a second loop-termination proof. Buffer-element iteration remains
effectful because it reads the actual shared heap.

The [structured client](##Examples.Language.OptionalBuffer) uses these as actual
source values: a pure helper returns `Option (Nat × Nat)`, a library returns
`Nat × Option (Buffer Nat)`, and its importing caller matches the optional view
before reading and updating a cell. Its `bump_contract` statement uses ordinary
buffer parameters, an `Array.modify` contents relation and a frame on the real
final heap. Constructors and projections are normalized left to right; matching
exposes a payload only in the selected `some` branch. A binding such as
`let (length, present) ← Library.inspect xs` or `some (length, offset)` uses
ordinary product patterns. The expression or call is evaluated once, and its
used fields are extracted by actual compiled projections. Source correctness, imported
contracts and the [compiled result](##Examples.Language.OptionalBufferCompiled)
all concern that one declared implementation.

Without `(pure)`, the existing `P.f` and `P.f_eq` interface still exposes
effectful, possibly partial actions with actual heaps and finite faults.
Those `Part` observations remain noncomputable, while the pure native functions
can be evaluated by Lean. Native execution and certified RAM instruction costs
are different runtimes; ordinary result equality assigns no execution cost.
A terminating Lean definition returning `Part α` may return `Part.none`:
constructing the action does not establish its `Part.Dom`. Nor does a defined
finite fault establish successful return. Use `FunctionTotal` or a strict native
triple for successful source termination; a host `termination_by` on action
construction alone is not that proof.

For effectful equations, the dedicated
[`source_eval` simp set](##Complexity.Language.Eval.Simp) removes transformer
administration after opening one generated `P.f_eq`. Supply actual read, write
and recursive-call equations to `simp [source_eval, ...]`; recursive function
bodies remain opaque. This preserves the real intermediate heaps and does not
turn faults into success. The [splay proof](##Examples.Language.Splay.Correctness)
combines this interface with a mathematical `Tree`, subtree-local memory frames
and one well-founded induction. Its representation supplies access bounds;
no proposed running time or RAM capacity is needed for source correctness.

State a mutable contract using standard `Std.Do` notation, rather than spelling
out the exception/state transformer and a large execution tuple. For example,
the splay theorem's conclusion is:

```lean
⦃fun heap => ⌜heap = initial ∧ Input key keys left right tree heap⌝⦄
  Implementation.splay keys left right (root tree) query
⦃⇓ result finish => ⌜Post key keys left right query tree initial result finish⌝⦄
```

Use `open scoped Std.Do Part.TotalCorrectness`. The standard `⇓` requires
successful return; it does not allow an exceptional outcome. `Input` states
the represented tree, unique node identities and actual buffer separation.
`Post` keeps the returned root, represented output tree, rotation certificate
and frame on the actual final heap. Its ordinary `Access` consequence states
inorder preservation and the search-selected root; BST order, unique identities
and complete key-array preservation have separate proved projection lemmas.
The [specification](##Examples.Language.Splay.Specification) is shared with the
RAM theorem, not a second implementation or an unchecked summary.

Every declaration also generates `P.f_contract pre post`, with the function's
ordinary curried parameters followed by the initial/final heaps. This is the
existing `FunctionTotal` contract, not another correctness interpretation.
`P.f_total_iff` proves its equivalence to actual successful evaluation.
For resource contracts, `P.f_onArgs bound` applies an ordinary parameter function
to the actual environment; `P.f_args` constructs that environment for a call.
These generated operations replace hand-written `Env.head`/`tail` chains.

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

The [buffer copy library](##Complexity.Language.Buffer.Copy) contains actual
`copyInto`, allocating `copy` and allocating `append` implementations. Their
contracts state ordinary Array contents and preserve observations of old views.
`copyInto` requires disjoint source and destination views, not different object
identities; disjoint slices of one object are permitted. Allocating `append`
allows its two inputs to overlap because the destination is fresh. These
operations currently store Nat cells and return mutable borrowed handles.
The contents theorem does not make their results permanently immutable or make
copying free in the separately proved RAM cost.

The [collection contracts](##Complexity.Language.Buffer.RepresentedCopy)
reuse those same implementations for Array, List and length-indexed Vector
views. For example, `append_list_length` combines `append_list_refines` with
`List.length_append`; the caller supplies no new loop proof. The
[resize implementation](##Complexity.Language.Buffer.Resize) allocates a new
buffer with the requested prefix and zero padding, retaining all old views.
It neither moves the original object nor changes an old handle's length.

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
giving a proved 27-instruction block before its continuation. Native allocating
List operations and the complete operation library remain open. Array and Vector retain
contiguous layouts. Reusing List theorems does not justify replacing linked
`cons` or `tail` with unmentioned array allocation or copying.

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

The opt-in [represented frontend](##Complexity.Language.Syntax.Represented)
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
callbacks from completed native families are supported too. General recursive
native blocks, dynamic callbacks and general element layouts remain unfinished;
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
and returning branch blocks. General native patterns and recursion remain
separate work. The local result slot and its copies are real source operations,
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

Conversely, [fold readiness](##Ram.LanguageCompiler.List.Fold.ready) and its
[callable resource certificate](##Ram.LanguageCompiler.List.Fold.functionResources_of_ready)
need no callback time bound. They reuse the independently proved finite source
loop through [indexed loop lifting](##Ram.LanguageCompiler.ArenaReady.while_of_exec_indexed).
The invariant tracks the actual cursor and remaining callback reservations;
real guard/body endpoints and immutable shared-tail observations pass between
rounds. The fold does not repeat its list or termination induction in the
resource proof. Its existing measured interface then applies the independent
cost certificate to that same ready execution. The native read-only
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
The fold wrapper gets its actual execution and bounds from the
[composable fold entry](##Ram.LanguageCompiler.List.Fold.arenaMeasured).
It supplies mathematical accumulator/list observations, callback correctness
and resources, admissibility, word ranges and remaining capacity. The shared
entry constructs the internal source arguments and reuses the existing traversal
proof; the caller does not assemble a resource-index tuple or another wrapper
totality/resource/cost contract. Its measured certificate is composed directly:

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

The [node action rules](##Complexity.Language.NodeRef.consM_spec) use the same
`ExceptT`/`StateT` proof interface as buffers. Default `@[spec]` rules describe
actual node allocation and typed lookup; separate `consM_list_spec` and
`readM_list_spec` rules expose ordinary cons contents and a shared tail through
the same linked representation. They preserve the real heap effects, including
old lists sharing the tail. The read statement's generated observation reuses
`readM` and its native specification; construction similarly reuses `consM`.
These actions also underlie the native construction path above. They do not
by themselves supply a complete persistent container operation library.

Mutable bindings use ordinary Lean `do` in the generated equation. `x := value`
updates an existing local, and `x ← action` rebinds it to the result of a real
source call, read, slice or allocation. Branch joins retain outer updates;
leaving an ordinary binding drops only that binding, without reclaiming its
object. Ordinary `let` and parameters are immutable.
Copying an existing buffer handle does not copy its contents or alter the heap.

`with_scratch do ...` explicitly gives fresh objects a lexical lifetime. Its
core `Stmt.scope` reclaims the fresh suffix on a safe exit while keeping the
current contents of older objects. A `return` still leaves the enclosing
function after cleanup; it does not merely return from the scratch block.
For an output that must survive, allocate it outside the scratch scope and use
the inner buffers only temporarily. No implicit copy or freeze is performed.

The safety premise `ScopeSafe initial finish control` says surviving locals
and any returned value are rooted in the entry object domain. `TotalWP.scope`
and `scope_compose` require this premise and apply the postcondition to
`finish.heap.take initial.objects.size`, not to a restored entry heap. The
native `Stmt.scope_action_spec` describes the same actual exit; a named block's
`spec` exposes its safe-body obligation. Mutable buffer cells contain only
scalars. Immutable heap nodes have explicit backward tail links, so retaining
a root's prefix also retains its chain. Node values use the entry-domain
rootedness rule, including when nested in products or options; rootedness alone
does not certify a typed complete list. `Exec.rooted_backward` preserves rooted
values and backward links together, including the tail exposed by `readNode`.
Its initial heap invariant is already supplied by the arena representation.
Node construction retains the same invariant by sharing a tail rooted in the
existing object domain, without a runtime traversal or validation check.

If the entry-root condition fails, source semantics retains the heap and reports
`regionEscape`, unless an earlier fault exists, in which case it preserves that fault.
Safe fault exits may reclaim storage but remain faults. The RAM backend certifies
safe exits only: it saves and restores the real allocator cursor, including
after an early return, without a runtime escape scanner or GC. Finite capacity
remains a separate backend premise. The [scratch consumer](##Examples.Language.Scope)
proves the actual nested/called source program using these rules and ordinary
array contents. Its [compiled theorem](##Examples.Language.ScopeCompiled) supplies
the separate physical workspace bound; exact peak-live-space analysis remains distinct.

[Evaluation adequacy](##Complexity.Language.Eval.Basic) distinguishes finite
faults from absence of a finite result. The
[composition equations](##Complexity.Language.Eval.Composition) preserve lexical
scope, actual callee results and early returns. The
[continuation interface](##Complexity.Language.Eval.Continuation) derives ordinary
monadic composition from the same evaluation: `Stmt.evalWith` runs its continuation
only after a normal outcome. Return and fault bypass it; function fallthrough is
the defined `.missingReturn` error. These proved rules justify the generated
function equations, without a second interpreter or a user-supplied host algorithm.

For example, the pure helper has an ordinary mathematical equation:

```lean
theorem increment_eq (n : Nat) : Bounded.increment n = n + 1 := rfl
```

The [remainder example](##Examples.Language.Remainder) similarly proves
`Implementation.remainder n d = n % d` using `Nat.mod_eq_sub_div_mul`, including
divisor zero, then transfers it through the generated total source contract.

For native `Std.Do` reasoning, `open scoped Part.TotalCorrectness` activates the
[strict partial-value WP adapter](##Complexity.Control.Part). It requires an actual
returned value: divergence cannot establish a postcondition vacuously. The
[verification bridge](##Complexity.Language.Eval.Verification) proves source
`FunctionTotal` equivalent to ordinary result equations and to native `ExceptT`
Hoare triples with false fault postconditions. It reuses the standard transformer
instances; it does not make `mvcgen` prove source termination automatically.
Function preconditions take the initial heap, and postconditions relate it to
the returned value and final heap. The native triple fixes the initial heap as
a ghost rather than identifying it with the post-state. Calls retain the
callee's actual heap even on failure. The
[heap foundation](##Complexity.Language.Heap) supplies `Buffer.Contents`, whose
mathematical view is a native array; reads and writes correspond to `getElem`
and `Array.set`, retaining aliases. The
[RAM representation](##Complexity.Computability.Ram.Compiler.Language.Heap)
relates complete shared objects and their views to actual memory, preserving
the relation through successful reads and writes. Its placement is proof data,
not a runtime object table. The
[operation bridge](##Complexity.Computability.Ram.Compiler.Language.HeapOperation)
executes real dynamic load/store expressions and retains their compiler-derived
counts, without claiming runtime fault checks. The source language now accepts
borrowed-buffer length, reads, writes and relative slices; calls and compiled
execution retain their actual final heap rather than restoring the initial one.

The [buffer example](##Examples.Language.Buffer) reads an element, calls a
branching helper, writes the result and returns a slice. Its ordinary native-array
specification describes the update with `Array.set`. After rewriting the generated
function equation, native `mvcgen` composes the public `readM_spec`, `writeM_spec`
and `sliceM_spec`; the author supplies contents and bounds, not monad implementation
equations. The write rule also retains its real write equation for alias/frame
reasoning. `FunctionTotal.triple_spec` turns a supplied source function contract
into a native continuation rule without unfolding the callee. The frontend
generates `P.f_spec` to apply it with ordinary named arguments. The buffer proof
uses:

```lean
have clampSpec := Implementation.clamp_spec clamp_total
rw [Implementation.clipHead_eq]
mvcgen [clampSpec]
```

The author still supplies read/write contents and bounds. The helper's full
contract carries its initial heap, actual result and final heap; the rule does
not require that heap to be unchanged. No contract is guessed or
registered globally, and no loop invariant is automatically synthesized.

For a real effectful composition, the existing source program also declares:

```lean
def boundedMapPair (xs : Buffer Nat) (ys : Buffer Nat) (limit : Nat) : Unit := do
  boundedMap xs limit
  boundedMap ys limit
  return
```

Named `Unit` calls are ordinary statements; non-`Unit` results require an explicit
binding. The [composition proof](##Examples.Language.TraversalComposition) passes
each callee's `boundedMap_total_frame` to the generated `boundedMap_spec` with
the corresponding arguments and contents. The first frame supplies the second
call's current input; the second preserves the first result. The resulting
contract retains both `Array.map` results and all initially valid views disjoint
from both buffers. Disjoint slices of the same object are allowed. Neither
callee body nor its array invariant is unfolded in the caller proof.
Calls can name local functions or functions from explicitly imported source programs:

```lean
source_program Client importing Library, Other where
  def compute (n : Nat) : Nat := do
    let result ← Library.compute n
    let updated ← Other.update result
    return updated
```

The libraries must be previously declared `source_program` families, available
through ordinary Lean imports or earlier declarations. Qualify a library call
with the family name used in the `importing` clause. Public headers persist in
Lean's environment; arbitrary Lean functions are not accepted as implementations.
The [typed source linker](##Complexity.Language.Linking.Basic) can now combine
separately declared tables while renaming their actual internal calls. An
embedding preserves every selected signature and body, not just an assumed
callee contract. The [observation theorem](##Complexity.Language.Linking.Eval)
equates each mapped native action with its original action, including divergence,
finite faults and their final heaps. `SignatureMap.eval` hides only the proved
parameter/result-type transport; it observes the actual target function.

The [linked examples](##Examples.Language.Linking) place the existing recursive
factorial after the traversal table, relocating its self-call, and reuse the old
factorial and array-map/frame proofs directly. Neither algorithm is reimplemented
or unfolded again. The [extension rule](##Complexity.Language.Linking.Extension)
adds new bodies already typed against the combined table, allowing real calls
from the client into imported libraries. Generated `Client.f_eq` equations
replace imported invocation observations by the original library actions through
the proved embeddings. The [named clients](##Examples.Language.Imports) therefore
reuse the old factorial and two-buffer frame proofs without source ASTs or table
indices; a second client imports the first with the same interface.

For each imported family, the frontend exposes `Client.imports.Library.map`
and `Client.imports.Library.embedding`; `Library` is the spelling used in the
`importing` clause. These source declarations do not depend on RAM. The
[function-contract rule](##Complexity.Language.Linking.Verification)
`FunctionTotal.renameCalls` transfers an existing library contract through the
embedding, handling the dependent argument and return types internally.

The separate [resource rules](##Complexity.Computability.Ram.Compiler.Language.Linking.Verification)
provide `FunctionRealizable.renameCalls` and `FunctionCostBound.renameCalls`
with the same interface. They preserve word width, call-nesting capacity and
the original bound. Their [lowering correspondence](##Complexity.Computability.Ram.Compiler.Language.Linking.Lowering)
retains the actual inferred function frame and call overhead; the
[cost theorem](##Complexity.Computability.Ram.Compiler.Language.Linking.ExecutionCost)
preserves exact counts and reflects arbitrary target executions. Source
observation equality by itself would not establish these resource claims.

The [compiled client](##Examples.Language.ImportsCompiled) reuses the imported
factorial's three contracts and the existing structural tactics, without another
recursive induction. Its real halted invocation includes the extra caller's
work and call depth. Code and stack capacity still concern the complete linked
program; an unrelated imported function may have different space requirements
or heap effects. No host callbacks or trusted cost annotations replace these proofs.

Import the [connection-layer tactics](##Complexity.Computability.Ram.Compiler.Language.Linking.Tactic)
to pass the original library theorems directly:

```lean
ram_source_call using (Library.realizable contents), (Library.total_frame contents)
  via Client.imports.Library.embedding
```

On a realization goal the first theorem supplies realizability; on a cost goal
pass the original library cost bound instead. The second theorem is the source
correctness contract in both cases. The tactic transports those contracts by the
embedding and invokes the existing staged call rule. It retains the actual
returned value and final heap, then stops at the next call. It neither chooses
a contract nor substitutes the library body. The function-level
`ram_source_realize (names) using feasible, specification via embedding` and
`ram_source_cost (names) using bound via embedding` forms use the same proved
transport; ordinary parameter names may be omitted.

The [effectful client](##Examples.Language.ImportsTraversalCompiled) calls the
imported traversal twice with different contents contracts. The first frame
preserves the second input in the actual intermediate heap, so the second call
does not reuse a stale pre-state. Both array results and the outside-both frame
appear together in the compiled invocation's represented final heap. The views
may be disjoint slices of the same object. Its instruction bound reuses the
original composition bound, with imported call overhead identified by the
lowering theorem; no loop-cost or array-correctness proof is repeated.

The typed core also has an effectful-guard `Stmt.while`. Its guard is an actual
Boolean-producing block: it runs in the current state on every iteration, and
even its false exit retains local and heap updates. A normally completing body
repeats the loop; a return exits the enclosing function. A guard that falls
through without returning a Boolean faults. `TotalWP.while_wellFounded` and
`while_variant` require mathematical descent only after a full normal cycle,
not on a false exit or early return. These are source rules, without a time budget.
The [native loop interface](##Complexity.Language.Eval.Loop) gives a one-step
equation for the same `Stmt.action` and `Stmt.while_spec` for strict `Std.Do`
reasoning. Its guard and body are actual source blocks, not a second host loop.
The [ordinary-local view](##Complexity.Language.Eval.Locals) represents the complete
lexical environment by ordinary values, retaining the final locals on every
exit. Its [loop rules](##Complexity.Language.Eval.Locals.Verification) take an
invariant and well-founded relation, or a natural-valued variant, on those values
and the current heap. The [continuation bridge](##Complexity.Language.Eval.Locals.Continuation)
runs the remaining function only on normal completion. These are proved changes
of view of the same source execution, not another implementation.
Named `while` and bounded `for` generate actual guard/body/loop observations,
one-step equations and mathematical block contracts. A `guard_contract` describes
the Boolean decision and actual state after testing; a separate `body_contract`
describes normal completion or early return. Their predicates take ordinary
mutable arguments and initial/final heaps. They are native strict triples,
packaged by [BlockSpec](##Complexity.Language.Eval.Locals.Specification), not a
second operational semantics.

Use `variant_contract` to compose these facts with a natural-valued measure,
or `wellFounded_contract` with an ordinary Lean well-founded relation. The body
starts at the actual post-guard state; a normal iteration must decrease relative
to the state before the guard. False exits and early returns need no descent.
Generated `guard_spec`, `body_spec` and `spec` apply a chosen contract to a native
continuation. Immutable captures are restored internally from proved execution
frames; preserving a buffer descriptor does not preserve its contents.
The older `variant_spec` and `wellFounded_spec` rules remain available for direct
native round proofs, as used by the scoped-allocation consumer. None of these
source rules asks for fuel or an instruction budget.

For pure finite Nat ranges, the shared
[`while_range_encoded_invariant`](##Ram.LanguageCompiler.RealizationWP.while_range_encoded_invariant)
rule reuses generated native correspondence and retains the supplied mathematical
invariant at normal exit. It supplies range termination, leaving the actual
guard/body word conditions and invariant preservation to the client. The
[structured accumulator](##Examples.Language.ScalarCompiled) uses it to connect
ordinary fold/sum correctness and its independent full invocation bound to the
same halted RAM result. In addition to launch capacity, its range conditions
include the final sum, computed stride and last actual cursor, which may exceed
the stopping endpoint. Its connection proof still selects generated local views;
that remaining transport is not a new mathematical proof of the algorithm.

The [loop-coordinate tactic](##Complexity.Computability.Ram.Compiler.Language.LocalsTactic)
normalizes generated local views without repeating their projection lemmas:

```lean
ram_source_locals StructuredRange.sum_loop1
ram_source_locals Implementation.boundedMap_loop1 at bound
```

The loop namespace selects its registered coordinate, native-encoding and frozen
range-endpoint equations. Standard locations also support `at h ⊢` and `at *`;
without a location only the target is rewritten. The tactic does not unfold
program bodies, callees, invariants, value-range predicates or costs, and does
not search for arithmetic proofs. Both the structured accumulator and mutable
traversal use this pass. Selecting the loop contracts and supplying their
mathematical obligations remain separate from coordinate normalization.

For a statement goal retaining its generated loop `Code`, the
[named-loop resource tactics](##Complexity.Computability.Ram.Compiler.Language.LoopTactic)
also select the capture view and its checked guard/body preservation proofs:

```lean
ram_source_loop_cost (remaining := fun locals _ => contents.size - locals.1)
  using (guard_contract xs limit contents), (body_contract xs limit contents)
  costs guard_costBound, body_costBound

ram_source_loop_realize
  using (guard_contract xs limit contents), (body_contract xs limit contents)
  total loop_contract xs limit contents heap
```

The supplied block contracts determine the invariant and actual guard/body
relations. The cost form applies uniform guard/body certificates; the author
still proves entry into the body, invariant preservation, decrease, positivity
and the initial invariant. The realization form converts the source loop
contract to totality, keeping its precondition separate from the resource
invariant. For example, the traversal's source precondition additionally carries
its outside-buffer frame. Routine true/false postcondition consequences are
discharged; other consequences, actual word/nesting proofs and invariant
preservation remain goals. The `enterBody` case names the true-guard implication.
The compiled traversal uses both entries without writing capture views, frame
theorem names, environment repacking or its own `BlockSpec → TotalWP` conversion.
Mathematical mutable-coordinate patterns remain in its proof leaves.

Apply these tactics before unfolding the named `Code`. Already expanded loops
and arbitrary potential functions can still use the public loop theorems below;
the cost tactic is the uniform-cost, linear-iteration specialization, not a
replacement for those general interfaces or automatic invariant discovery.

The [read/helper/branch/write traversal](##Examples.Language.Traversal) writes
`for i in [:xs.length]`. Its invariant describes the processed prefix and unread
suffix of an ordinary array. Independent guard/body contracts feed the loop
contract; the author proves array identities, actual frames and descent rather
than constructing a nested triple for a whole iteration. The generated `spec`
then composes that contract with the function's continuation. Selecting these
contracts and mathematical contents remains explicit. The
[compiled traversal](##Examples.Language.TraversalCompiled) reuses this source
proof to establish the same array result and an independent linear instruction
bound for the actual halted invocation. Its word ranges, preloaded heap
representation and code/stack capacity are explicit. The
[realization loop rules](##Complexity.Computability.Ram.Compiler.Language.Realization.Loop)
reuse source termination without a second decreasing measure, and the
[ordinary-local cost rules](##Complexity.Computability.Ram.Compiler.Language.CostBound.Locals)
compose actual guard/body bounds and the source invariant. Their fixed-capture
rules reuse generated lexical preservation, leaving only mutable locals and the
heap in the author's invariant and potential. `StmtCostBound.while_contract_fixed`
and `RealizationWP.while_contract_fixed_of_total` consume the same independent
guard/body contracts. The library extracts their mathematical facts at the
actual execution points using `BlockSpec.post_of_eq`; authors do not reconstruct
operational observation equations. They supply the logical connection from a
true guard to the body's precondition, range evidence and numerical potential
inequalities. The source invariant and termination proof are reused. The
`BlockSpec.mono` consequence rule strengthens the input and weakens either
successful relation, while retaining the original precondition as a usable
fact. Mathematical invariants, frame composition and potential inequalities
remain explicit; correctness contracts themselves contain no instruction budget.

`Buffer.Disjoint` permits different objects or disjoint `Set.Ico` intervals of
the same object. `Buffer.PreservesOutside xs initial finish` says that every
initially valid disjoint view retains its ordinary contents. Its `write`, `trans`
and `mono` rules derive and compose this fact from actual successful writes;
overlapping aliases remain allowed and observe their real updates. This is a
contents-preservation relation, not whole-heap equality or handle ownership.
The traversal's `boundedMap_total_frame` returns both the array-map result and
this frame at the same final heap. Its compiled `boundedMap_execute` exposes
that frame, the mathematical array result and the instruction bound against one
typed `FunctionExecution` outcome. The outcome retains the actual halted runner
and complete final machine memory; callers do not reconstruct the old witness
tuple. The two-call and imported clients use the corresponding
`boundedMapPair_execute` entry points. Neither array correctness nor
register-level simulation is proved again. The original `runUntil` theorems remain
available as lower-level compatibility interfaces.

For recursion, the [source contract rule](##Complexity.Language.Verification.Recursion)
`FunctionTotal.verify_wellFounded` supplies complete callable specifications at
smaller mathematical indices through Lean's `WellFounded.induction`. A fixed
function selector gives ordinary recursion; a varying selector supports mutually
recursive functions with different signatures. The index is mathematical proof
data, not runtime fuel, an instruction budget or a stack-depth bound.
For the supported pure fragment, the [named factorial](##Examples.Language.Factorial)
uses Lean's native termination machinery:

```lean
source_program (pure) Recursive where
  def factorial (n : Nat) : Nat := do
    if n == 0 then
      return 1
    else
      let previous ← factorial (n - 1)
      return n * previous
    termination_by n
    decreasing_by simp_wf; simp_all +zetaDelta; omega
```

The author supplies this decreasing argument once. Generated correspondence
reuses the native recursion principle to prove successful source execution with
the same result and unchanged initial heap, without a second implementation
induction. Ordinary `Nat` induction separately proves the mathematical equation
`Recursive.factorial n = Nat.factorial n`; the generated `_total` contract then
transfers that result to the actual source program.
The [compiled factorial](##Examples.Language.FactorialCompiled) reuses that same
source theorem. Its separate realization proof uses `ram_source_realize (input)`
with the recursive realizability and source contracts. It bounds intermediate
values by the representable factorial result and bounds nested calls by `n`;
parameter environments and statement-level target conversion are internal.
Its independent
cost induction uses `ram_source_cost (input)` and, in the successor case,
`ram_source_cost (input) using ih`, with actual generated call overhead. Argument
environments are opened internally; ordinary induction, recursive-input facts
and the final arithmetic inequality remain the author's proof.
The resulting halted-runner theorem returns factorial, preserves shared entry
memory and retains the generated code and stack-capacity premises. The linear
word-RAM instruction bound is in the numeric argument `n`, not its binary bit
length or the cost of arbitrary-precision multiplication. These backend range,
nesting and cost arguments do not repeat the source termination proof. Pure
mutually recursive families and a convenient named proof interface for effectful
recursion remain open; automatic pure correspondence is not a promise of
automatic termination transport for arbitrary effectful actions.

The [compiled buffer invocation](##Examples.Language.BufferCompiled) reuses this
source proof and derives the read cell's range from the input heap representation.
Its separate bound concerns the same read/helper/write/slice program and its
actual returned descriptor and updated heap. Borrowed aliases remain allowed;
the example does not establish a general mutable-loop proof interface.

The [scalar example](##Examples.Language.Scalar) calls a real increment helper,
assigns a local in the selected branch, then proves its returned value equals `min (n + 1) limit`
using ordinary Nat facts. Its `increment_eq` and `boundedIncrement_eq` proofs
reason about native values; the latter unfolds its definition, simplifies
`Id.run` and `Id.instMonad`, reuses the helper result and splits the mathematical
comparison. Rewriting the generated `P.f_total` contract with these equalities
supplies the source contract required by compilation, without a second
implementation induction. Default effectful declarations retain `P.f_total_iff`
for ordinary curried preconditions and actual initial/final heaps.
Direct source-WP rules remain available when a
compositional contract is the preferred starting point. The
[compiled invocation](##Examples.Language.ScalarCompiled) supplies only source-level
range and call-nesting facts, then reuses that mathematical proof. In particular,
`n + 1` must fit even when the final minimum is small. These conditions do not
include a proposed instruction budget. The
[structural tactics](##Complexity.Computability.Ram.Compiler.Language.Tactic)
now open ordinary parameters and compose the scalar realization rules:

```lean
ram_source_realize (n limit) using increment_realizable, increment_total
all_goals omega
```

The supplied callee facts remain opaque. Environment projections and argument
packing are simplified internally; genuine scalar ranges, callee preconditions
and sufficient call nesting remain mathematical goals. This is a scalar proof
pass, not automatic discovery of invariants or general recursive contracts.

[Generic simulation](##Complexity.Computability.Ram.Compiler.Language.Simulation)
handles lexical layouts, real callees and returned fields.
[Static validity](##Complexity.Computability.Ram.Compiler.Language.Validity)
chooses the register boundary and discharges checked-compilation conditions;
[execution transfer](##Complexity.Computability.Ram.Compiler.Language.Execution)
then gives the existing halted runner, actual result and same-execution count.
Code and stack capacity remain explicit. Shared-state preservation is derived
from the actual lowered program, not assumed from restored caller registers.

The compiler lowers each statement child once and uses a private return flag to
skip tails after a return; calls restore the caller's flag.
[Exact code-size formulas](##Complexity.Computability.Ram.Compiler.Language.CodeSize)
include each branch once, plus actual argument and callee-frame expansion.
Static code length is not elapsed time: the running program selects one branch,
and even a returned path pays the flag checks in enclosing sequences.

[Source cost rules](##Complexity.Computability.Ram.Compiler.Language.ExecutionCost)
now observe the same realized source execution. `ExecutionCost` counts its
lowered core; a complete function adds two transitions for flag initialization.
Its empty final dispatch has been removed, with a proved saving of three static
instructions and an unchanged register bound. The generic statement wrapper
with an external continuation still uses five additional transitions on return.
`callCost` derives internal-call overhead from the actual compiler, including
the callee body and frame, without a user-supplied ABI price. `callCost_eq_add`
separates the body count from the fixed generated overhead, so a recursive bound
can use ordinary arithmetic without unfolding frame or return layouts.
The [measured simulation](##Complexity.Computability.Ram.Compiler.Language.MeasuredSimulation)
proves these are real machine counts. Budget-free behavior simulation erases
this same proof instead of maintaining a second structural induction.

`FunctionCostBound` is a separate conditional bound: it does not establish
termination or repeat the mathematical postcondition. Its counts are
[independent of word width, call capacity and realization proofs](##Complexity.Computability.Ram.Compiler.Language.CostDeterministic).
[Cost transfer](##Complexity.Computability.Ram.Compiler.Language.CostExecution)
identifies the existing `bodyTime`; `FunctionRealizable.runUntil_le` combines
the source bound with the original correctness and realization contracts.
The complete invocation bound adds the outer calling convention and final halt
exactly once.

The [typed execution interface](##Complexity.Computability.Ram.Compiler.Language.FunctionExecution)
publishes the result without rebuilding that runner tuple for every example.
`FunctionCapacity` contains the existing positive-width, code and stack
conditions; `FunctionLaunch` adds the actual argument ranges and represented
starting memory. Neither contains the algorithm's correctness predicate or a
proposed time bound. `FunctionRealizable.execute` composes source correctness
and realizability; `execute_le` adds a separately proved instruction bound.
Its `FunctionExecution` result retains actual source evaluation, returned words,
halted runner state, body time and complete step count. `nextEntry` carries the
entire returned physical memory into a later invocation. The factorial and
splay consumers use the same interface, including factorial's preservation of
arbitrary initial RAM memory below the heap boundary.

For allocation and reclamation, the corresponding
[arena execution interface](##Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution)
uses `FunctionArenaLaunch` and `FunctionArenaExecution`. It additionally retains
the actual final placement and cursor, rooted inputs and a measured invocation
at the specified call depth. `ArenaReady.execute` needs no time budget;
`FunctionArenaRealizable.execute` adds the independent source specification.
Its `memory` is an `ArenaRep` on the actual halted machine, and `nextEntry` keeps
that complete memory for a later call. The
[scratch client's](##Examples.Language.ScopeCompiled) public theorem now states
only mathematical contents, final cursor and the actual workspace conclusion.
The runner, return-field and representation facts come from this shared result.
The workspace rules bound all actual accesses and out-of-envelope writes at
every prefix; they do not claim an exact reachable-live-space count.

Use the [structural bound rules](##Complexity.Computability.Ram.Compiler.Language.CostBound)
to compose source costs. `StmtCostBound` bounds the existing execution observation;
its primitive, sequence, branch, return and call rules hide case analysis on
`ExecutionCost`. `FunctionCostBound.of_stmt` adds the returning-body wrapper once.
`ram_source_cost (n limit) using increment_costBound` applies these rules to the
scalar consumer and compares the inferred bound with its requested bound.
For several callees, `using [recursiveBound, rotateRightBound, rotateLeftBound]`
selects among the supplied contracts at the actual call. Their own preconditions
remain proof obligations; the author need not construct a dependent function
table. `ram_source_cost_intro (names)` opens only the function-body rule and
ordinary parameters, leaving mathematical case analysis before the structural
pass. It expects the existing body wrapper's `core + 2` bound shape.
Its uniform bound needs no proof of the minimum;
result-dependent bounds can reuse an existing source contract through the call
rule. A guard proved from source values and local facts selects only its actual
branch through `StmtCostBound.ite_true` or `ite_false`. If neither decision can
be proved, the tactic retains the uniform maximum of both branches. The default
call form infers a uniform numerical continuation bound. A uniform bound may
still need a callee's postcondition to establish a later call's input.
Neither instruction prices nor mathematical correctness proofs are duplicated.

The [compiled traversal](##Examples.Language.TraversalCompiled) also lets the
solver infer uniform budgets instead of copying numeric constants. `guardCost`
and `bodyCost` pair one natural-number witness with a proof for every local
environment and heap; the witness is introduced before those quantified values.
`ram_source_cost_step` determines it from the actual source structure and supplied
callee certificates. `ram_source_cost_intro` similarly infers the function wrapper
around the supplied loop bound. Direct, two-call and imported clients reuse the
resulting `boundedMapBodyBound` rather than repeat its expression.
`StmtCostBound.whileLinearBound` includes the normal-loop and false-exit charges;
its lemmas leave the remaining-iterations inequality to the author. This does not
discover invariants, nonlinear recurrences or dependent numerical bounds.

For a numerical bound depending on the actual result and final heap, provide
the ordinary bound function explicitly:

```lean
ram_source_call (next := fun (value : Nat) finish => remainingBound value finish)
  using callee_cost, callee_total
```

The command leaves the continuation's cost proof and the final numerical
comparison under the supplied callee postcondition. It reuses
`StmtCostBound.call_of_spec_le` or `call_seq`, according to the actual source
statement; no hypothetical returned value or unchanged-heap premise is added.
The scalar consumer uses the returned increment to select different branch
bounds. The two-buffer consumer separately demonstrates transport of the actual
final heap and its frame facts. An author still supplies the mathematical bound;
the command does not infer arbitrary result-dependent recurrences.

`StmtCostBound.call_seq` handles a standalone call followed by another statement.
It reuses the supplied callee contract to pass the actual final heap and ordinary
postcondition to the next bound, keeping caller-local restoration and empty
result-scope cases inside the shared proof. The
[compiled two-buffer composition](##Examples.Language.TraversalCompositionCompiled)
uses its uniform specialization twice and reuses the original traversal's bounds.
Its actual halted invocation retains both arrays and the outside-both frame in
the same represented final heap. Word ranges, code capacity and space for
pair/traversal/helper remain explicit; these are not a proposed instruction budget.

For such composition, start with `ram_source_cost (xs ys limit)` without `using`.
The structural pass opens ordinary parameters and stops at the first call.
On that call goal, select its contracts explicitly:

```lean
ram_source_call using (boundedMap_costBound leftContents),
  (boundedMap_total_frame leftContents)
```

This handles one call, retaining its actual result, final heap and postcondition,
then stops at the next call. In the two-buffer proof, the first frame establishes
that the second input still has `rightContents`; the next `ram_source_call` uses
the corresponding right-side contracts. The full proof, including input facts
and the final arithmetic inequality, is `boundedMapPair_costBound` in the linked
example. After the calls have fixed the inferred bound, `ram_source_cost_step`
simplifies its generated constants in the remaining inequality; ordinary
arithmetic proves the requested budget. Argument packing, scope restoration and
intermediate structural bounds are inferred by shared rules. The same command works after `ram_source_realize`,
with a realizability contract in place of the cost contract.
Contracts are never invented or searched for globally. Multiple explicitly
supplied contracts are matched against the actual callee; the original single
`using` mode reuses its supplied contract throughout the pass. Loops remain explicit proof
boundaries in either mode, and neither mode invents an invariant or a frame fact.

For typed loops, `StmtCostBound.while` uses a state-dependent potential. The
guard and body bounds follow the actual state; normal iterations account for
the remaining potential, while false exits and early returns discharge their
own remaining work. The final false guard is counted. This is a conditional
cost rule for the same execution, separate from the well-founded termination
rule; the structural tactic does not yet choose or apply loop invariants.

The frontend supports `Nat`, `Bool`, `Unit`, borrowed buffers, products, options,
lexical bindings, actual named calls, branches and returns. Nested addition, multiplication, saturating
subtraction, division, remainder and comparisons are normalized left to right
into actual primitive bindings. This also applies to guards and call arguments.
The [remainder example](##Examples.Language.Remainder) implements
`n - (n / d) * d`, reuses the ordinary Nat identity, and derives the actual
compiled result with a separate instruction bound. Divisor zero is included;
no artificial subtraction-order condition is required.
Named effectful `while`, bounded `for`, option matching and initialized allocation are supported as
described above. Product/option construction, projection and local assignment
are covered by the same structural realization and cost tactics. General sums,
recursive data representations, general pure `while`, mutually recursive pure families and richer
callee selection, recursive proofs and data-dependent bound automation remain
unfinished. Costs are currently derived
for successfully realized executions, not an instrumentation theorem for
every unrestricted source execution.
The checked fragment does not establish the complete source proof and
specification interface needed by general mutable collections and recursion.
Optimizing code size does not imply every execution is faster.
The executable word-RAM workflow and maintainer interfaces below remain available.

Compiler maintenance is a separate, active proof workflow. The
[layout rules](##Complexity.Computability.Ram.Compiler.Language.Layout),
[return-flag preservation](##Complexity.Computability.Ram.Compiler.Language.Control)
and measured simulation compose actual register updates and calling conventions.
The same layout indexes every actual value field. Parameter packing and fresh
receivers use those indices and the existing register-update rules; Unit has no
dummy field. Buffers have two fields, their actual base address and length;
products concatenate component fields and options add a tag before their payload.
Absent payload fields are zero padding, not a manufactured buffer. Selected
payload copying is real emitted work, included in the exact instruction count.
Sequential multi-field copies preserve
their operands through proved destination separation or actual self-copy
identities, not an assumed snapshot. `RegisterMap.Regular` proves the field
layout needed to update an existing variable without changing another live
variable; parameter layouts and fresh bindings supply it automatically.
Maintainers may use these lemmas directly, without frontend metadata. Preserving
caller registers does not imply that a callee leaves memory or I/O unchanged.
The [frame-effect rules](##Complexity.Computability.Ram.Compiler.Effects) include
`FramePreserved.frameSaved`: a saved caller frame within the protected stack
interval remains valid after the callee. Ordinary and local call proofs reuse
this rule, while retaining genuine heap effects and address bounds.

## Choose a specification

For the existing word-RAM language, start with `Ram.Source.TypedFunctionContract`. Its precondition
describes typed arguments and caller state; its postcondition describes the declared
`Word w`, `ArrayRef w` or `Unit` result and shared-state effects. The argument encoder
and result kind reuse the [source-value representation](##Complexity.Computability.Ram.Source.Value).
`TypedFunctionContract.of_wp` proves a body directly, and `wp_call` gives the typed value
to the continuation. `of_raw` reuses an existing raw contract; `raw` connects a chosen typed
input to the existing independent time rules. These are views of the same implementation,
not new execution relations, and require neither a `main` nor a time budget. See
[typed function contracts](##Complexity.Computability.Ram.Verification.Function.Typed).

`Ram.Source.FunctionContract` remains the raw field-list interface used by existing
implementation proofs. Its precondition describes word arguments and caller state;
its postcondition describes returned fields and shared-state effects.
`Ram.Source.FunctionExec` defines those observations through the function's real body and
return expressions: the returned list is `f.results.map callee.eval`, with every field
evaluated in the same final callee state. Scalar, array and `Unit` returns have one,
two and zero fields respectively. A mathematical specification is a property of that execution,
not a replacement implementation.

The `input` and `outputRev` fields in `Ram.Source.State` are shared stream state, not the
function's arguments and return value. Only actual source `read` and `write` operations
consume or append stream words. Function contracts quantify over entry states satisfying
their precondition; they do not automatically assume empty streams or unchanged effects.
In the factorial contract, the precondition only restricts the argument list and the
postcondition says `finish = entry`. Thus `function_runs` proves termination and the
factorial result for arbitrary initial stream contents, while preserving those contents.
The optional `read`/call/`write` main is verified separately.
Choosing `Source.State.initial []` in a wrapper only chooses an entry state: it does
not add a read, supply function arguments through a stream or prove independence
from other entry states.

The [factorial example](##Examples.Ram.Factorial) returns a word and preserves caller state.
The [array-copy function](##Complexity.Computability.Ram.Array.Function) instead changes
represented arrays in shared memory. Its public contract hides parameter registers but
retains genuine address-range, length and non-overlap assumptions.
`Ram.Source.FunctionContract.wp_call` reuses a contract at another function's call site;
the continuation receives the returned fields, the proved postcondition and preserved caller locals.
The [local-binding sample](##Examples.Ram.LocalBindings) retains this raw interface and composes its call rule twice
through `ram_total_apply`. Its direct proof uses the source declaration from
[getting started](##ComplexityDocs.GettingStarted) and the existing `square_contract`:

```lean
theorem squaredNorm_contract (heapLimit : Nat) (x y : Word w) :
    Source.FunctionContract functions.program heapLimit 1 functions.function.squaredNorm
      (fun args _ => args = functions.arguments.squaredNorm x y)
      (fun _ entry value finish => value = [x * x + y * y] ∧ finish = entry) := by
  ram_total_vc args entry rfl [functions.body_eq.squaredNorm, functions.result_eq.squaredNorm]
  ram_total_apply (square_contract heapLimit x) [functions.function_lookup.square]
  ram_total_apply (square_contract heapLimit y) [functions.function_lookup.square]
```

`ram_total_vc args entry pattern [facts]` starts the `FunctionContract` using
`Ram.Source.FunctionContract.of_wp`: declared arguments are bound, and the
postcondition observes the real return fields and shared state. The pattern
`rfl` here substitutes the specified argument list. Each `ram_total_apply` uses
the supplied function contract and lookup fact without unfolding `square`'s body.
Here simplification automatically substitutes the postcondition's equalities for
the returned value and final state into the continuation. No manual `rintro` or
final `rfl` is needed. Non-equational postconditions still leave ordinary continuation
goals. This proof needs no separate intermediate-state specification, register
arithmetic or stack layout.
Argument and result arities must match the callee signature. Unresolved arity, frame
and return-expression read-safety obligations remain explicit. `of_body` remains
useful when a body refinement or invariant is already available; the tactics do not
discover invariants or select reusable contracts automatically.
The sample's independent `squaredNorm_bodyTime` theorem identifies the same body's count
as 46. It includes both calls to `square`, not `squaredNorm`'s own final return expression
or its enclosing calling convention.

The same `ram_total_vc` supports `TypedFunctionContract` through its `of_wp` rule.
The [three-array merge](##Complexity.Computability.Ram.Array.Merge.Function) uses
`ram_total_vc` and `ram_total_apply` to call the already verified core: the remaining
goals are its three represented arrays and the post-call list representations.
It does not need another typed tactic or a second proof of the merge loop.

For a named declaration `p`, use `p.eval.f` for function-value equations and
`p.bodyTime.f` for separate body-count equations. These generated entry points take
the declared word or array parameters, then `heapLimit` and `entry`. They specialize
`Ram.Func.evalTyped` and `Ram.Func.bodyTime`, observing the same actual invocation through
mathlib's `Part`. The generated value interface decodes the declared field shape
to `Word w`, `ArrayRef w` or `Unit`, without a default for a missing field. Its equation has the form
`p.eval.f ... heapLimit entry = Part.some (value, finish)` and includes termination;
the typed result and shared state are both retained. The
[factorial function-value sample](##Examples.Ram.FactorialFunction) hides its canonical
entry state once and proves agreement with every actual caller state. Subsequent
mathematical propositions mention only its argument and observed value.
This is a noncomputable proof view, not executable ordinary Lean function syntax.
General stateful functions still depend on shared entry state, and insufficient heap
capacity can make an observation undefined.
The ordinary executable `p.apply.f` interface described below is separate;
it does not make these `Part` observations computable.

`TypedFunctionContract.eval_spec` transports the typed postcondition to this view;
`FunctionExec.evalTyped_eq_some` also transfers a concrete execution using the generated
`results_length` equation. Neither bridge asks clients to split result lists or reconstruct
an array reference from a specification.
`Ram.Source.FunctionContract.eval_spec` transports any postcondition to the raw field-list
view; the declared shape connects it to the generated typed view. The postcondition can
be a mathematical relation, not necessarily a reference algorithm.
`Ram.Source.FunctionContract.eval_with_timeBound` adds a separate bound to the same
invocation's `Ram.Func.bodyTime`. Neither observation is defined using the proposed
result property or time bound. Body time excludes this function's own final return
expressions and enclosing call overhead; it includes completed calls inside its body.

To execute a declared function, use `p.run.f` with the same typed parameters,
`heapLimit` and `entry`, rather than the noncomputable `Part` observation.
It specializes `Ram.LocalCompiler.Function.runUntil` and returns
`Option (Ram.RunResult (Ram.State w))`, retaining machine state, actual steps and
stopping reason. It requires no instruction limit and does not discard effects.
The underlying `runUntil_of_execution` bridge derives a returned
machine result and its actual count from `FunctionExec`, with no proposed time budget.
Code and stack still have to fit the selected word width. To identify the count,
`runUntil_eq_of_execution` combines `FunctionExec` with a separately proved
`bodyTime = Part.some bodySteps` equation. The
[runnable factorial sample](##Examples.Ram.FunctionRun) uses this second bridge with
`FactorialFunction.bodyTime_eq` to identify the value and full count of the same
application used by `#eval`. General divergent programs do not
return a nontermination flag; use `Ram.LocalCompiler.Function.run` when an operational
limit is desired. Unlike body time, the complete run counts the outer call, return
and halt. The generated entry point does not prove capacity or construct represented arrays.

For an ordinary executable value, use `p.apply.f ... heapLimit entry h`; use
`p.applyState.f ... heapLimit entry h` for its typed result and reusable source shared state,
or `p.runTotal.f ... heapLimit entry h` for the complete machine result.
All three require `Ram.LocalCompiler.Function.Halts` for those exact arguments and
entry state: the actual `runUntil` equals `some result` and `result.reason = .halted`.
An `isSome` proof alone would also admit faults and is not enough for this interface.
The [total-call bridge](##Complexity.Computability.Ram.Compiler.Local.Function.Total)
`halts_of_execution` derives this fact from budget-free `FunctionExec` with the
compiled-code and stack premises. It does not require a cost theorem.
`halts_of_typedContract` takes an existing typed contract and its precondition;
`halts_of_contract` is the corresponding raw-contract rule. Both work
without making the client first extract a returned value and execution witness.

For these runtime bridges, use `ram_run_apply theorem [facts]` from
[runner proof automation](##Complexity.Tactic.Ram.Run). It applies the supplied theorem,
selects the same standard compiled call-and-halt code used by the runner, and checks
static compilation, lookup and code-fit obligations at that use site. Generated
declaration bindings and supplied facts are used only for those static goals;
unresolved goals remain explicit.
The [factorial](##Examples.Ram.FunctionRun), [sum](##Examples.Ram.ArraySum) and
[slice](##Examples.Ram.ArraySlice) clients use it for halt, value and separate step proofs
without maintaining private `rawLink`, compilation and code-length declarations.
Stack capacity, representation, overflow and the supplied correctness or time theorem
remain explicit proof obligations. This is proof automation, not another runtime wrapper
or a guarantee that every `ram_def` compiles and fits every word width.

For a complete invocation's upper bound, `ram_run_bound theorem [facts]` also
compares the bridge's proved bound with the requested one. It reuses `ram_bound`
to normalize actual argument, return, frame and halt overhead; supply the
generated return-expression equation where needed. The copy, slice and
source-composition consumers no longer hand-expand those instruction counts.
Unresolved stack and mathematical obligations remain visible, and the requested
bound is never passed to the runner as fuel.

`runTotal` performs `Option.get` on the actual runner output; generated `apply` decodes
its returned fields using the declared result shape. The proof argument is in `Prop`
and erased at runtime, not a supplied answer extracted from a specification.
Use `Ram.LocalCompiler.Function.applyTyped_eq_of_execution` for the generated typed value;
the underlying `apply_eq_of_execution` identifies raw fields. When starting with
a typed contract, prefer `Ram.LocalCompiler.Function.applyTyped_spec`: provide
its precondition and a mathematical implication from the postcondition to the
desired value property. The lower-bound and slice-sum equations use this rule
without unpacking an execution or reconstructing the returned fields.
`runTotal_correct_of_execution` also retains the source-visible final-state observation.
Neither normal halt nor projecting a result property asserts that the body has no effects.

`Ram.LocalCompiler.Function.applyStateTyped_eq_of_execution` identifies the typed pair
with `(value, finish)`, while `applyStateTyped_spec` transfers a typed contract's
postcondition directly. The [typed runtime bridge](##Complexity.Computability.Ram.Compiler.Local.Function.Typed)
uses the same compiled run and does not introduce another runner.
The [merge application](##Examples.Ram.Merge) uses `applyStateTyped_spec` directly:
`Function.merge_spec` describes its three arrays and preserved frame, and
`Function.merge_contents` rewrites the actual destination to standard `List.merge`.
The sorted-permutation corollary then uses existing list mathematics.
For recursive operations on two buffers, `ArrayAt.reassemble_prefix_of_frame_two`
and `reassemble_suffix_of_frame_two` combine a changed half with the preserved half
using the operation's actual two-buffer frame. These
[shared array rules](##Complexity.Computability.Ram.Array.TwoBuffer) already shorten
both recursive merge-sort stages without fixing registers, return values or
equal buffer sizes in the rules. Slice containment, disjointness and the changed
half's length remain explicit premises.
The [typed recursive declaration](##Complexity.Computability.Ram.Array.MergeSort.Function)
uses these rules through its [representation stages](##Complexity.Computability.Ram.Array.MergeSort.Stages).
Its correctness proof is ordinary induction on list length, generalizing over
the source and scratch references so that both actual recursive calls reuse
the same hypothesis. `TypedFunctionContract.renameCalls` transports imported
operations through the existing embedding; `mono_depth` increases a genuine
call-depth capacity without introducing a time budget.
The [executable client](##Examples.Ram.MergeSort) then states sortedness,
permutation and a contents-level `StateM` equality using existing list theorems.
Scratch may change and remains represented; those effects are not erased by
the mathematical contents projection. The typed correctness calls use
`TypedFunctionContract.wp_call_restored`: their continuation sees the actual
shared effects with caller bindings already restored, so subsequent calls need
no accumulated register-restoration equalities. Ordinary result assignment still
occurs. `FunctionTimeBound.call_seq_typed_restored_at` gives the separate time
proof the same restored-state interface; the default remaining-reserve variant
also removes hand-selected intermediate budgets. Mathematical representation and
whole-algorithm cost arguments remain explicit.
The raw `applyState_eq_of_execution` identifies `(values, finish)`.
Its `returnState` projection keeps entry registers, takes actual target memory below
`heapLimit` and entry memory outside it, and retains actual input/output effects.
Safe execution preserves out-of-heap source memory, so this recovers the entire
source final state without equating it with the target's private stack.
`applyState_spec` transfers any existing `FunctionContract` postcondition to that
pair, with the contract's precondition and the compilation/capacity premises.
The [copy client](##Examples.Ram.ArrayCopyFunction) decodes its zero fields as `Unit`
and uses this rule for its destination contents, frame and stream-preservation claims,
then reuses them to call sum on the
returned state; it does not reopen the copy loop.

The [factorial application](##Examples.Ram.FunctionRun) proves ordinary equations
`factorial_eq_mod` and `factorial_eq`, and positivity using mathlib, about its
executable `factorial n hstack : Nat`. The latter two retain the no-overflow premise.
These values can be executed with `#eval`; their mathematical equalities use the
proved execution bridge, not kernel computation by `rfl`. The underlying word width,
capacity and entry-state restrictions are not removed by an ordinary return type.

Use `Ram.Source.TotalContract` when the precondition and postcondition directly describe
the source state. `Ram.Source.TotalRelContract` also lets the postcondition refer to the
entry state, which is useful for framing unchanged data.

Use `Ram.Source.Refines` when an ordinary Lean function is the clearest description of the
result. Its arguments have the following shape:

```lean
Refines program heapLimit depth stmt inputRep outputRep f
```

For every mathematical input `x`, an entry state satisfying `inputRep x` safely terminates
in a state satisfying `outputRep (f x)`. The predicates connect words and memory to the
mathematical values; they may also carry encoding, capacity and frame assumptions.
They do not require a bijection between an entire heap and a value.

Here is the refinement proof from [the small I/O example](##Examples.Ram.Verification).
Its `main` reads a word, increments it, and writes the result:

```lean
theorem main_refines (rest out : List (Word w)) :
    Refines [] 0 0 main
      (fun x s => s.input = x :: rest ∧ s.outputRev = out)
      (fun y t => t.input = rest ∧ t.outputRev = y :: out)
      (fun x : Word w => x + 1) := by
  ram_refine x s ⟨hin, hout⟩ [main, increment, hin, hout]
```

This is modular word addition. The proof also retains the input tail and prior output;
it does not silently reinterpret the computation as unbounded natural-number addition.

## Use mathematical theorems at the interface

Once you have a refinement, prove properties of `f` using ordinary Lean and mathlib.
`Ram.Source.Refines.spec` transfers a theorem about `f x` to the implemented result.
`Ram.Source.Refines.with_postcondition` retains the property in the representation for
subsequent composition.

Reuse an operation's existing contract before unfolding its body. In particular:

- `Ram.Source.Refines.seq` composes two refinements through their shared intermediate model.
- `Ram.Source.Refines.congr_fun` changes the model by a proved equality of functions.
- `Ram.Source.Refines.equiv` changes mathematical coordinates through an equivalence.
- `Ram.Source.Refines.transfer` handles related, possibly lossy models when the functions
  respect the chosen relations.

The [graph-degree sample](##Examples.Ram.GraphDegree) is a concrete use of this boundary.
Its implemented operation is the [reusable array sum](##Complexity.Computability.Ram.Array.Sum).
The graph proof only identifies the represented row's list sum with mathlib's
`SimpleGraph.degree` and applies the existing function contract. It does not reprove
the traversal, register updates or unchanged-memory facts. The row is explicitly
preloaded; converting an abstract graph to that layout would need its own implementation.
Its `sum_eq_degree` theorem also states a direct equality about the ordinary executable
`ArraySum.sum`. It rewrites `ArraySum.sum_eq` and the mathematical adjacency-row sum,
without opening an execution relation or a calling-convention proof.

The array-sum source accepts `xs : array`, and `sumPair(left : array, right : array)`
calls it as `call sum(left)` and `call sum(right)`. The generated argument builders take
`Ram.ArrayRef` values; `array.Rep heapLimit xs entry` supplies the mathematical contents,
exact length and existing memory representation. `sum_function_contract_of_ref` and
`sumPair_function_contract` expose the returned list sums and unchanged shared state.
The two read-only references may overlap: this client does not need a disjointness premise.
Mutating operations still need their own aliasing and frame conditions. Passing a reference
does not prove its representation or execute a list loader. The
[array-argument sample](##Examples.Ram.ArrayArguments) uses
`sumFunctions.eval.sumPair left right heapLimit entry` for the mathematical result and
`sumFunctions.run.sumPair left right heapLimit entry` for actual compiled execution.
Its explicit heap and stack premises are separate from any time estimate; the
mathematical list concatenation does not allocate a new runtime array.

The [local-slice client](##Examples.Ram.ArraySlice) binds
`let window ← call slice(xs, offset, count);` and calls the imported sum on
the returned array reference. `slice` declares `: array` and returns
`subslice(xs, offset, count)`. `Ram.ArrayRef.Rep.subslice` supplies the ordinary
`(xs.drop offset.toNat).take count.toNat` representation;
`Ram.ArrayRef.Rep.subslice_end_lt` carries the parent's strict endpoint bound to
the selected interval. The slice contract carries the returned reference's representation
to the sum call, which reuses sum's existing contract rather than its traversal proof.
Descriptor evaluation and both returned fields are part of the compiled call, not
a host-side loader or copy. Containment, representation
and non-wrapping addresses remain explicit, and the postcondition preserves the
entire caller state, including arbitrary initial stream contents.

After `sumSlice_eq` identifies the ordinary executable result, the
[slice-properties client](##Examples.Ram.ArraySliceProperties) proves
`sumSlice_zero`, `sumSlice_whole` and `sumSlice_partition` by ordinary list reasoning.
The whole-slice result agrees with `ArraySum.sum`; the partition result adds the two
slice results modulo the word range. These proofs use the value equations and
standard `List.take`/`List.drop` identities, not execution relations, register updates
or loop proofs. The partition theorem compares returned values and does not compile
its two host applications into one program or supply their combined cost.

For a scoped `for` with one scalar expression update,
[the source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Expression)
`Ram.Source.Array.ForIn.Expression.function_contract` uses the generated body and
return equations to infer the private slots. Sum and count share its cursor progress,
termination and framing proof. The first argument is an array; additional word
parameters are retained automatically as the full `array.args ++ captures` prefix.
Count therefore needs no separate invariant to preserve its target.
The client still proves the actual expression's read safety and evaluation as the
mathematical fold step, using the supplied parameter equalities where needed.
Array representation, address range and the ordinary `List.foldl` identity also
remain mathematical obligations. The separate measured rule derives iteration
costs from compiled instructions; a host-language callback is not a free operation.
The [count client](##Examples.Ram.ArrayCount) then derives permutation invariance
directly from `List.Perm.count_eq`. It uses the typed reference contract for
`count(xs : array, target)`, with independently represented arrays that may live in
different heaps. The theorem equates returned counts, not the states or the work needed
to construct those arrays. Its `runCount_eq` theorem also covers an actual compiled
call with the target word as a runtime argument, returning the count independently
of stream output. The [sum client](##Examples.Ram.ArraySum) likewise reuses the function
contract and measured execution for its value equation and runner, without another
raw loop proof. Its ordinary `sum` application takes representation/range evidence
and a stack-capacity proof, both erased at runtime; `sum_eq` identifies the actual
returned natural number. No mathematical list is passed as executable data.
Fixed verified helper calls have their own
[source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Function);
these two conveniences remain specialized scalar folds. General bodies use the
invariant rule below; short-circuiting still needs a separate language interface.

These rules operate on fixed source statements. They do not turn an arbitrary mathematical
function into executable code. See [data models](##ComplexityDocs.Models) for array, matrix,
partial-map and framing interfaces.

## Loops and recursive calls

For a loop, choose a mathematical invariant and a well-founded progress argument.
`Ram.Source.Refines.while_wellFounded` relates the real guard and body to an abstract step
and eventual result. If a decreasing natural number is enough,
`Ram.Source.Verification.TotalWP.while_variant` provides a direct total-correctness rule.
The guard, representation and safety obligations remain at the implementation boundary.

For an arbitrary body of `Stmt.forIn`,
`Ram.Source.Verification.TotalWP.forIn` handles setup, each actual element load
and the two cursor updates. Supply an invariant at the loop head and prove the
body from `ForIn.loadedState` into an invariant after `ForIn.advanceState`.
The body must preserve the remaining count of its loaded entry state. The rule
uses ordinary natural descent, not a proposed time budget. The invariant need
not describe a single accumulator or unchanged heap: it can relate several
locals and mutable data to ordinary mathematical values.

This is an implementation-side combinator, not automatic invariant inference.
The loop-head invariant is not assumed to survive the element assignment.
Each load reads the current heap; body effects reach the next iteration.
Initialization evaluates length after assigning the pointer, and address safety
is required only when the guard is nonzero. The rule does not assert that an
arbitrary body preserves the original array contents or pointer trajectory.
See [general foreach correctness](##Complexity.Computability.Ram.Verification.ForIn).

For a forward traversal that preserves its private cursor locals, prefer
`Ram.Source.Verification.TotalWP.forIn_indexed`. Supply a payload
`invariant : Nat → State w → Prop` for the mathematical iteration number.
The rule owns the pointer/count relation, count subtraction, termination and
exit-index argument. The body proof receives `i < n` and the payload at the
pre-load state, starts at the actual current-heap element load, and establishes
the next payload after `ForIn.advanceState`. It does not assume the payload
survives loading its element local. Cursor preservation is an endpoint premise,
so writing and restoring a cursor is allowed; static destination exclusion is
one way to prove it. Memory and I/O may change. The setup equations still use
sequential expression evaluation, and only executed addresses need be safe.

If the payload is insensitive to the two private cursor locals, use
`Ram.Source.Verification.TotalWP.forIn_indexed_of_frame`. Prove once that
`State.LocalFrame {pointer, remaining}` preserves it. Then initialization starts
from the original state and the body only proves `invariant (i + 1)` at its own
endpoint; the shared rule transports this through cursor setup and advance.
Only those generated assignments use the unchanged-shared-state frame, not the
arbitrary body. Map uses this interface without unfolding `advanceState`.

The independent `Ram.Source.TimeBound.forIn` accepts a uniform conditional body
bound `B` and preservation of the remaining count on completed body executions.
It adds the actual setup expression lengths, `(B + 14) * count` and the remaining
four setup/final-guard instructions. No body totality or heap-purity premise is
needed for this conditional result. The existing helper-call traversal reuses
this rule; its separate prefix-dependent bounds remain available.
See [general foreach costs](##Complexity.Computability.Ram.Verification.Time.ForIn).

The [in-place map operation](##Complexity.Computability.Ram.Array.Map.Function)
is a mutable consumer of these rules. Its typed contract takes a borrowed array,
returns `Unit`, and produces a representation of `xs.map transform` together
with the outside-array frame and preserved I/O. The helper is a statically linked
source function, proved to implement `transform` on the original list elements.
The mathematical function is only its specification, not a runtime callback.

The [map client](##Examples.Ram.ArrayMap) uses the existing DSL:

```text
fn mapSquares(xs : array) : Unit {
  for i, x in xs {
    let y ← call Scalar.square(x);
    xs[i] := y;
  }
  return;
}
```

Its correctness proof reuses the imported square contract and the common map
theorem. Index initialization and increment are real generated assignments;
both loop bindings stay within the body. The operation proof uses the indexed
rule to maintain the ordinary
updated-prefix/unread-suffix list without its own private cursor/count invariant.
The body directly composes a function-call WP, `Ram.Source.Array.store_contract`
with its count forgotten, and an assignment WP. The continuation receives the
updated `List.set` representation and frame instead of rebuilding an execution
endpoint. It reads each original element before replacing it.
Empty arrays are admitted; an unused final pointer may wrap
at the address-space endpoint. The actual descriptor length remains word-sized.

The independent map bound is `(C + 23) * length + 8`, where `C` is the helper's
proved body bound plus its actual compiled calling overhead. It requires a
uniform conditional helper bound on one-word inputs, not helper totality.
For this imported square, the full compiled invocation has bound
`46 * xs.length + 71`; `applyState_contents` observes `List.map` from the same run.
The map changes memory, so a returned `Unit` alone is not its mathematical output.
No host list loading or allocation is included.

This is a reusable operation, not a general named-invariant elaborator or runtime
higher-order function. Arbitrary mutable bodies still use the explicit invariant
rule; input-dependent helper costs need a corresponding ordered cost proof.

For local binding adapters, `Ram.Source.State.LocalFrame writes before after`
packages unchanged memory and I/O with mathlib's
`Set.EqOn after.regs before.regs writesᶜ`. Its assignment and composition rules
let a proof carry all unaffected parameters together instead of rebuilding a
chain of individual register updates. This is an endpoint relation, not an
execution or a description of every write event. An expression still needs its
read-safety and evaluation proof, and every actual assignment keeps its cost.

Function entry initializes the entire local frame. To reason that new locals
preserve parameters, compare subsequent states with `entry.enter args`, not
with the original caller's register bank. `State.restore_eq_of_shared` uses
proved memory/input/output equalities to restore the original caller without
requiring preservation of discarded callee locals. See the
[local-frame rules](##Complexity.Computability.Ram.Source.State.Frame).

For effectful bodies, `SafeExec.regs_eq_of_not_mem_writtenRegs` instead preserves
each local outside `Stmt.writtenRegs`, without requiring an unchanged heap.
The [static local-frame rules](##Complexity.Computability.Ram.Source.Frame) use
ordinary sets and include only result destinations for calls. Map and helper-call
traversal discharge their count-preservation condition by simplifying this set,
not inspecting callee executions. Static exclusion is sufficient, not necessary;
the original semantic rule still admits writing and restoring a local.

The [named search](##Complexity.Computability.Ram.Array.Search.Function) directly
opens its generated body, proves initialization, and reuses the shared loop
contract. Its time proof follows the same source decomposition. The actual
remaining `while` determines the private local slots before their separation
is checked; no extra function-body recognizer or exported loop-scoped midpoint
is needed. The shared mathematical invariant and its initialization proof remain
explicit, so this is not general automatic invariant discovery.

For a callable recursive function, ordinary mathematical induction can prove
`Ram.Source.FunctionContract` directly. The [factorial example](##Examples.Ram.Factorial)
uses natural-number induction in `function_contract`: `ram_total_vc args entry rfl`
starts the function proof from its generated body and return equations, and
`ram_total_apply` applies the induction hypothesis at the smaller argument.
This main correctness proof does not construct a `TotalSpec`, name local registers
or prove stack-frame equations. The mathematical induction, argument-range facts
and word-arithmetic lemmas remain explicit; no time budget enters the proof.

`Ram.Source.Refines.call` can package a proved function specification as a refinement
of a call. Argument binding and return adaptation are handled at this boundary;
shared heap and I/O effects survive return, while the call theorem restores the
caller's other locals.

The API chapters on [control flow](##Complexity.Computability.Ram.Verification.Control),
[total recursion](##Complexity.Computability.Ram.Verification.Recursion.Total) and
[calls](##Complexity.Computability.Ram.Verification.Call) give the exact premises.

Use `Ram.Source.Recursion.TotalSpec` when the specification also needs the complete
callee-body endpoint. Its well-founded rules establish that stronger conclusion;
`Ram.Source.Recursion.TotalSpec.verify_wellFounded_function` presents smaller
invocations as argument/result contracts while retaining the body-state obligation.
The factorial example's separate `recursive_total` theorem instead unfolds one body
step and reuses `function_contract` to prove its local-state endpoint explicitly.
A returned value and restored caller state do not determine the callee's discarded
locals. This stronger interface is available when needed, not a prerequisite for
the function's main correctness proof. Neither route automatically chooses a
termination argument or compiles an arbitrary ordinary Lean definition.

## Stateful mathematical models

Use `StateM σ α` when a sequence of updates is easier to describe with state and a returned
value. It is an optional semantic model, not a second program every user must write.
Lean's `Std.Do.Triple` and `mvcgen` can prove its mathematical specification.
The same I/O example contains:

```lean
def incrementState : StateM (Word w) PUnit := do
  let value ← get
  set (value + 1)

open Std.Do in
theorem incrementState_spec (x : Word w) :
    ⦃fun state => ⌜state = x⌝⦄ incrementState
    ⦃⇓ _ state => ⌜state = x + 1⌝⦄ := by
  mvcgen [incrementState]
  simp_all
```

`Ram.Source.Refines.stateM_spec` transfers such a triple through a proved refinement of
`model.run`. `Ram.Source.Refines.stateM_spec_refines` keeps the native postcondition for
later operations. `Ram.Source.Refines.stateM_bind` composes returned values and state;
its mathematical continuation may depend on a returned value, but the corresponding source
statement is fixed and must obtain that value through its representation.

There are also [call](##Complexity.Computability.Ram.Verification.StateM.Call) and
[finite traversal](##Complexity.Computability.Ram.Verification.StateM.Traversal) bridges.
The call bridge represents returned fields as an ordinary list. Its register-observation
form requires distinct destinations to recover every field from the final registers;
the source call itself permits repeated destinations with last-write-wins assignment.
`mvcgen` verifies the mathematical model: it does not compile arbitrary Lean code or discharge
the model-to-memory connection. Reuse an existing bridge where one is available.

## Automate the routine work

`ram_refine x s hs [facts]` starts a refinement proof;
`ram_total_vc s pattern [facts]` starts a state-based total-contract proof;
`ram_total_vc args entry pattern [facts]` starts a `FunctionContract` directly.
Precondition patterns include `rfl` and `⟨rfl, hbound⟩`. Closed frame bounds may
be discharged automatically; unresolved obligations remain ordinary Lean goals.
Use `ram_total_apply contract [facts]` to apply a supplied operation, function or
recursive specification while keeping its implementation opaque. The dedicated
`ram_bindings` set supplies declaration-generated argument fields, lookups and
static parameter/result/local counts, including imported functions. Authors
still choose the contract and typed input, but need not repeat caller/callee
argument-builder definitions. Bodies, return expressions and mathematical
representation lemmas are not registered in this set.

For a named function whose initialization needs mathematical reasoning, use
`ram_total_start args entry pattern` to apply the existing function rule without
advancing the body. Then

```lean
ram_total_init functions.function.lowerBound at initial with bindings
```

follows the actual leading assignment statements, stopping before calls or
control flow. `initial` names the current source state. The visible locals
become ordinary Lean values such as `initial.xs : ArrayRef w` and
`initial.lo : Word w`; `bindings.xs.base`, `bindings.xs.length` and `bindings.lo`
relate these values to their actual source bindings. Nested locals such as the
search midpoint are not visible before entering their scope. An array local is
exposed only after its two field assignments have both executed.

The [named search proof](##Complexity.Computability.Ram.Array.Search.Function)
uses these facts with `Search.Pre.invariant`, then applies its existing loop
contract. It does not write a separate `State.enter`/`setReg` initializer.
The independent time proof uses `ram_time_start` and `ram_time_init` with the
same syntax, but applies the existing conditional time rules and charges the
actual assignments. Both initialization forms accept optional `[facts]`;
unsolved safety or affordability goals remain explicit. Neither form invents a
loop invariant or advances through a call.

To enter the next source conditional, select its branch explicitly:

```text
ram_total_branch f then at current with bindings [facts]
ram_total_branch f else at current with bindings [facts]
ram_time_branch f then at current with bindings [facts]
ram_time_branch f else at current with bindings [facts]
```

`then` requires the actual guard to be nonzero; `else` requires it to be zero.
Selecting a branch does not assume that condition: unresolved guard, read-safety
or time-affordability obligations remain ordinary goals. The step enters that
branch's lexical scope and advances its leading initializers, stopping before
another conditional, call, loop or other effect. Statements following the
conditional are retained; an omitted `else` executes the actual empty branch.

The [recursive sort implementation](##Complexity.Computability.Ram.Array.MergeSort.Function)
starts its large-input case with `ram_total_start`, followed by
`ram_total_branch sortFunctions.function.sort then at initial with bindings`.
Supplied range facts prove the guard. The actual source declarations then produce
`initial.middle : Word w` and `initial.left`, `initial.right : ArrayRef w`.
Both descriptor assignments complete before an array local becomes visible.
These values are passed to the existing recursive and merge contracts; no raw
slots or separately reconstructed initializer state are needed. Halving,
slice containment, disjointness and changed-heap reassembly are still proved
with the existing mathematical lemmas.

The [separate time proof](##Complexity.Computability.Ram.Array.MergeSort.FunctionTime)
uses `ram_time_start` and the corresponding `ram_time_branch`. Its rules retain
the actual guard evaluation, branch jumps and field-assignment costs; they bound
completed executions without using the initialization's total-correctness proof.
The proof starts from the original whole-body bound, with no hand-selected
intermediate branch reserve. The recurrence and proof that the complete work
fits that bound remain explicit, while remaining allowances follow from the
actual operations.

Without a cursor, these entry points require the named function's whole body.
An initialization or branch step records its exact lexical block and next child
only on the remaining code goal, so another such step can continue there.
The actual code is rechecked at that fixed position: no search for an equal AST
or re-elaboration of embedded source terms is used. This does not locate an
arbitrary prefix after unrelated proof tactics have advanced it.

The generated Lean lets are snapshots at the named state, not live readers of
later registers or heap contents. They remain usable in ordinary call proofs;
sort's `Unit` calls restore the caller locals containing its descriptors.
Representations of changed arrays still require the actual callee postcondition.
Ordinary call tactics do not advance the source cursor or automatically bind a
new source-local result name. Entering loaded loop-body scopes and elaborating
source-level invariants remain unfinished. See
[source-directed initialization and branches](##Complexity.Tactic.Ram.Source).

For a typed function call, `ram_total_apply contract on input [facts]` selects
the actual mathematical input and passes the returned value and shared effects
to a continuation with caller locals restored. It only attempts to close the
lookup, result-count, argument-read and argument-value obligations completely,
using declaration equations and locally generated source-binding facts.
The functional precondition, call-depth condition and continuation retain their
original form. In particular, supplying a slice definition to match runtime
arguments does not also expand every represented slice in the continuation.
Merge sort uses this form for both recursive calls, merge and copy-back.

Use `ram_total_store represented at index := value [facts]` to write one element
of a represented array. It applies the existing array-store contract to the
actual `TotalWP` store, opening one leading sequence when needed. No address
expression, value expression or destination register needs to be repeated.
The continuation retains the real updated state, a representation of
`contents.set index value`, and the outside-array frame. The
[map implementation](##Complexity.Computability.Ram.Array.Map.Correctness) uses:

```lean
ram_total_store h.array at i := (transform xs[i])
  [indexFits, h.base_eq, h.index, arrayAddr]
```

Only completely solved side conditions are discharged. Index bounds, current
representation, read safety and address/value equations otherwise remain visible;
the continuation is not simplified. A representation survives local-register
changes by its definition, but cannot be reused across a genuinely changed heap
without a proof. The tactic neither advances the next statement nor supplies
the next invariant. See [array automation](##Complexity.Tactic.Ram.Array).

Use `ram_total_bind mid hmid [definitions, facts]` on a `TotalWP` assignment
or a sequence beginning with one to name that assignment's actual word value.
The continuation receives `mid` and `hmid : mid = entry.eval expression` without
expanding the value or advancing later statements. The optional list unfolds
only the supplied definitions before applying the rule. Read safety is closed
only when `ram_simp` proves it; otherwise it remains a separate goal.
The [search body proof](##Complexity.Computability.Ram.Array.Search.Total) uses
this to reason about one named midpoint in both branches. The name is local to
the proof continuation, not an exported loop variable; array-result binding,
layout inference and invariant inference are not supplied by this tactic.

`ram_model [facts]` simplifies observations, and `ram_word [facts]` normalizes word arithmetic
with the available range conditions. Remaining obligations are ordinary Lean goals.

Supply representation equations and mathematical facts through these tactic arguments or
Lean's usual `simp` mechanism. The tactics do not infer loop invariants, invent no-overflow
hypotheses or turn modular arithmetic into exact arithmetic. Their API is under
[total verification](##Complexity.Tactic.Ram.Total) and
[model simplification](##Complexity.Tactic.Ram.Model).

## Reuse contracts for included functions

The [source-composition sample](##Examples.Ram.FunctionComposition) includes the
existing copy and sum declarations as `Copy` and `Sum`, then calls them inside one
new function. `functions.importMap.Copy` gives the old-to-new function index map;
`functions.embeds.Copy` proves that the relocated implementation belongs to the
combined table. The [function-linking rule](##Complexity.Computability.Ram.Source.Function.Linking)
`Ram.Source.FunctionContract.renameCalls` transports the original contract through
this embedding, retaining its arguments, returned value and shared-state postcondition.

The public `Ram.Source.Array.copy_function_typed_contract_of_ref` accepts a proof-level
pair of array references, encoding the same source pointer, destination pointer
and source length. Its destination length follows from represented input and
the equal-length premise, not a fourth runtime argument. The result is `Unit`. The sample
relocates this contract and applies its `wp_call_restored` rule with
`ram_total_apply`; declaration-generated bindings supply the lookup facts.
Copy's postcondition supplies both complete `ArrayRef.Rep` assertions, including the one needed by sum,
whose contract is reused through `functions.embeds.Sum`. The standalone
`call Copy.copy(...);` has an empty result list and no dummy destination.
Its postcondition and shared-memory effects still reach the continuation through
the same call rule. This differs from discarding a word or array result, whose
fields are still evaluated and received into private destinations.
Relocation does not discharge representation, equal-length or
disjointness premises. The proof composes the existing contracts without expanding
either callee loop; the generated `applyState` result belongs to one compiled run,
unlike the host-level sequencing in `ArrayCopyFunction`.
Merge sort's final copy uses this same reference contract. The raw and word-triple
typed contracts remain available; neither source signature nor execution cost changes.

The same sample's `imported_sumPair_eval` transports the existing two-array execution
through `functions.embeds.Sum` to `functions.eval.Sum.sumPair`. This also exercises
relocation of the imported function's own two calls to sum, without reopening them
or their loops. Imported aliases export lookup, argument and all six observation/run
interfaces; body equations and local-register names remain with the original declaration.
Generated `params_eq` and `locals_eq` equations are also available under imported
aliases. They expose calling-convention sizes without unfolding the callee body.
The separate time proof reuses the same functional postcondition: `ram_time_apply`
with `on input` passes copy's destination representation through restored caller
bindings and derives the remaining sum-call reserve from the overall body bound.
The proof still establishes that the complete copy call fits; neither a register
equality nor a hand-selected intermediate reserve is needed. The bound belongs
only to the time proof, not the correctness contract or executable call.
See [proving complexity](##ComplexityDocs.Complexity).

## Publish and link a verified implementation

Use `Ram.TotalComponent.ofNamed` to package a fixed named program with its
`Ram.Source.TotalContract`, shared input/output representations and safety capacities.
There is no time-bound field. `Ram.TotalComponent.comp` links independent function tables
and composes their total correctness on the actual intermediate representation.

Heap and call-depth capacities are still required for safety, and the output-size guarantee
supports later composition. These are not proposed instruction budgets.
`Ram.TotalComponent.runs_observed` exports an actual halted execution before time analysis.
See [budget-free components](##Complexity.Computability.Ram.Component.Total).

## Attach time and export the result

`Ram.Source.TimeBound` bounds completed measured executions; alone, it does not prove that
one exists. Combine it with the correctness proof using
`Ram.Source.TotalContract.with_timeBound` or `Ram.Source.Refines.with_timeBound`.
The resulting contract bounds the same safe terminating execution.

If a continuation has a uniform bound at every intermediate state,
`Ram.Source.TimeBound.seq_const` adds its bound to the first command's bound
without requesting a functional contract. Map uses this for its actual
store/assignment tail. State-dependent continuation bounds still need the
relevant intermediate facts; the uniform rule does not establish them.

For a reusable program, establish a scalar, input-size-based time envelope through
`Ram.TotalComponent.TimeBoundOn`, then use `Ram.TotalComponent.withTimeBound` to obtain
a resource-aware `Ram.Component`. A bound depending on the full input can first be
majorized by such an envelope.
The generated code and non-time guarantees are unchanged; existing component certificates
and polynomial-time interfaces remain available.

Correctness can also be exported without a time estimate.
`Ram.Source.Refines.compile_observed` transports represented outputs to an actual halted
target execution; `Ram.Source.Refines.compile_observed_with_timeBound` adds the separate
time bound. Code fit, stack capacity and output-observation transport are explicit premises.
The [backend chapter](##ComplexityDocs.Backend) explains these premises and the extra
instructions counted at the whole-program boundary.
-/
