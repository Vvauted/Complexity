# Source syntax and control flow

This document records executable syntax, its source meaning and the supported
structured-control fragments. Mathematical views do not select another program.

[Design overview](../HIGH_LEVEL_LANGUAGE.md) · [Roadmap](../ROADMAP.md)

## Programming model

Ordinary closed structures with direct scalar/scalar-product fields now have a
checked path through the default declaration. `source_type` derives their encoding and
constructor/projection equations; one source declaration can construct,
pass, return and project them while calling an imported source helper. The
[`Scalar`](../../Examples/Language/Scalar.lean) consumer proves the ordinary native
function equation and reuses generated `_refines` and `_total` contracts. Its
[`compiled consumer`](../../Examples/Language/ScalarCompiled.lean) uses the shared
range/cost rules and publishes the same actual halted RAM result, without a
per-algorithm register or representation adapter.

Finite Nat ranges also retain native structures as mutable accumulators across
actual source calls. `StructuredRange.sum` covers a dynamic positive stride,
a structure-valued helper call before the loop and another call in each round.
Its ordinary mathematical proof uses `List.foldl_hom` and `List.sum_eq_foldl`;
generated correspondence supplies total source correctness without a second
loop proof. Generated native guard/body equations and range endpoint/stride
selectors also feed the shared `StmtCostBound.while_range_encoded` rule.
The complete function-body's conditional instruction bound includes its pre-loop
call, setup, all rounds and source return, without consumer-written capture
indices, block-contract adapters or division-count descent. Its checked
finite-word realization reuses the shared invariant-preserving range rule, and
`structured_range_sum_execute_le` supplies the same halted RAM result and full
invocation bound. The final sum, last actual cursor (which may exceed `stop`),
computed stride and launch capacity retain explicit range conditions. The
connection proof selects its loop contracts and views. The shared
[`ram_source_locals`](../../Complexity/Computability/Ram/Compiler/Language/LocalsTactic.lean)
pass normalizes that loop's local coordinates and registered structure encodings,
without a consumer-written list of view or projection lemmas. Ordinary-parameter
resource rules should still remove the remaining contract/view setup.

The range example above retains the `(pure)` compatibility preparer, whose
structure support is narrower than the default represented declaration.
Neither entry compiles arbitrary Lean datatypes or dependent fields. Raw-to-native
reconstruction for automatic curried total contracts is available only for supported
layouts whose encode/rebuild roundtrip is checked; it is proof-side transport,
not a decoder for every representation or an uncharged runtime conversion.

### Values and operations

Implemented values are mathematical `Nat`, `Bool`, `Unit`, borrowed Nat/Bool
buffers, typed immutable Nat/Bool node references, and recursively nested native
`Prod` and `Option` values. A node reference occupies one word containing its
actual placed address, not its mathematical object identifier. Products
concatenate their actual fields; options place a tag before a fixed payload.
`none` has zero padding and `some` carries its actual payload. Unit still occupies
no fields. This encoding is used at calls, returns and assignments, not only in
proof-local tuples. The current surface does not add an explicit `BitVec w` type;
the backend's word representation does not change source Nat arithmetic to modular arithmetic.

Constructors, `.1`/`.2` projections and option matching use the same left-to-right
normalization as arithmetic. The selected `some` branch binds its payload once;
leaving that binding retains changes to outer locals and the actual heap.
Ordinary tuple syntax `(a, b, c)` normalizes to Lean's right-associated `(a, (b, c))`.
`none` requires an expected Option type or an explicit type annotation. Pure
mode permits recursively heap-handle-free products/options; hiding a borrowed
buffer or node reference inside either constructor does not make a function pure.
The current match syntax has explicit `none` and `some pattern` branches (in either
order). Immutable lets, call-result bindings and `some` payloads accept nested
product patterns and `_`. They evaluate the supplied expression or call once,
then project the used fields through actual source primitives. Duplicate binders
are rejected. General constructor matching and user-defined inductive types
are not implemented.

The [imported structured client](../../Examples/Language/OptionalBuffer.lean) uses
a pure `Option (Nat × Nat)` helper and a library returning
`Nat × Option (Buffer Nat)`. Its ordinary array/frame contract and
[compiled result](../../Examples/Language/OptionalBufferCompiled.lean) describe the
same selected read/write and four actual RAM return fields. Nested borrowed
views retain recursive rootedness and non-escape conditions; mutable buffer cells
remain scalar rather than gaining unchecked pointers.

Use a typed context and typed variable references internally. A context position
is a lexical binding, not a target register. Surface names and source locations
are retained for diagnostics and proof display.

Use an administrative-normal-form core: variables and literal values are atoms;
arithmetic, comparisons, reads, writes, calls and other operations are explicit
nodes whose results are bound before use. The scalar surface accepts nested
arithmetic and comparisons, normalizing them left to right into actual primitive
bindings in lets, returns, guards and call arguments. Fresh intermediate names
are hygienic and do not capture user variables. Atom materialization, moves and returns can still require
target instructions and are included in backend accounting.

Nat comparisons also accept `>`, `≥` and `>=`. Equality and disequality on
`Nat` and `Bool` accept `=`, `==`, `!=` and `≠`; Boolean expressions accept
`!`, `&&` and `||`. Conjunction and disjunction short-circuit: the right-hand
side's bindings stay inside the branch that needs them, rather than being
evaluated before the left-hand decision. These operations lower through the
existing core primitives and branches, with the actual emitted instructions
included in execution-cost accounting.

There is no runtime `pure arbitraryLeanTerm` escape hatch. A mathematical
`List.map`, `Nat.factorial` or sorting relation is freely usable in a
specification, not automatically an implemented primitive. Executable extensions
require a core definition or a proved implementation, representation contract
and cost connection. Ghost values and proofs cannot decide runtime branches
unless the corresponding computation is present in the program.

### Binding, control and functions

Support lexical `let`, `let mut`, assignment, sequencing, conditionals,
indexed array traversal, `while`, first-order calls and recursive functions.
The core records actual scope and binding, not a flat map of display names.

Statement `if condition then ...` may omit `else`: the false branch skips the
body and continues with the current locals and heap. This does not add general
value-level `if` expressions or arbitrary named calls inside expressions;
the existing explicit call forms remain in use.

Typed `let x : T ← do ...`, `← if ...` and `← match ...` (Option/List) value
bindings share the state-carrying mathematical boundary for modeled bodies,
including the supported finite-range/Option local-return fragment. The model
carries the returned payload and final outer mutable state into the continuation,
related at the actual final heap. Direct conditional/match bindings retain their
return markers inside the selected arm, with the selector outside; no extra raw
join is introduced. This is not a generated unchanged-heap exact equation or
support for arbitrary patterns, mutation or general `while` models.

Effectful `for i in [:stop]` and `for i in [start:stop]` use half-open ranges
and unit steps, with an immutable iteration index. Endpoints retain their
entry values: a literal or lexically immutable local/length can be reused;
other expressions are captured once. `for x in xs` retains the entry buffer
view but reads each cell from the current heap, so earlier writes through an
alias are visible. Both forms elaborate to the existing while semantics;
an early return leaves the enclosing function. Positive explicit steps are supported when the generated proof can establish
positivity, including a dynamic `k + 1`; a general proof-bearing stride
parameter, `break` and `continue` remain open. The checked mutable traversal uses
the same generated loop-contract interface.

The default represented frontend also generates a mathematical `forIn` model
and checked correspondence for fully modeled `if`/`Option` finite-range bodies
with mixed continuation and function-return branches. These use the actual
`Control.returned`/`whileReturn`, not an added local value block or pending slot.
A returned (`some`) round retains its actual payload and final heap without a
cursor increment or an extra false guard. Raw lowering is unchanged; no new RAM
cost bound follows. Automatic action correspondence and refinement also cover
a checked two-level finite-range nest with an inner function return. Normal and
function-returning finite ranges also support enclosing self-calls with descent
from fixed captures or the actual range bound. Termination preprocessing supplies
`index < stop` while ordinary model equations remain `foldl`/`forIn`; generated
correspondence reuses one native termination argument. This does not establish
arbitrary nested-loop support: general mixed local/function completion and full
models of arbitrary heap mutation remain open.

In the retained `(pure)` compatibility API, finite ranges generate a native total
iteration over the same normalized body. A shared finite-iteration theorem connects it to the
existing source while semantics; generated totality retains every initial heap.
The iterative factorial consumer proves the result through ordinary Lean folds
and mathlib multiplication facts, without another well-founded source proof.
General pure `while` and buffer iteration remain outside this pure fragment;
the roadmap distinguishes implemented constructs from exercised combinations.

The mutable extension uses one source state containing typed local values and
the shared heap. Assignment changes a lexical value, not a named machine
register. Loop invariants describe the current source locals and object contents.
Explicit loop-carried values may later be a proved normalization, but an SSA
translation is not a prerequisite for mutable source semantics or proof rules.

Leaving a lexical binding removes its local slot from the actual final state;
it does not restore the entry heap or undo assignments to outer locals. A call
uses its actual arguments and the current heap. Return restores the caller's
locals and retains the callee's final heap, including effects before a fault.

Specify normal continuation and function return as different control outcomes
from the start. A return crosses nested blocks and loops and is caught by the
function boundary; sequencing executes its tail only on normal continuation.
The scalar compiler already handles returns through nested bindings, branches
and sequences using a private flag, without duplicating the remaining code.
Loop lowering and the named loop frontend propagate the same control outcome.
The generated loop rules take an invariant and either a natural-valued variant
or a well-founded relation on mutable locals and the heap. Immutable captures
are fixed by proved lexical preservation. Authors still supply the mathematical
invariant and descent proof.
Option matching has checked source evaluation, branch-specific resource rules
and real tag/payload lowering. `break/continue`, general sums and recursive data
remain subsequent constructs; their control, representation and costs must be proved.

First-order functions are sufficient for the initial recursive algorithms.
Static specialization may later support generic combinators; dynamic closures,
arbitrary dependent runtime types and a general effect-handler system are not
prerequisites. Contracts are reusable by callers within the current source
program. The [source linker](../../Complexity/Language/Linking/Basic.lean) now
provides signature-preserving call renaming and checked embeddings of actual
bodies. Its [observation theorem](../../Complexity/Language/Linking/Eval.lean)
preserves the entire partial action, so existing mathematical contracts transfer
without re-proving recursion, loops or heap effects. The frontend's `importing`
clause now resolves previously declared source families, retains their complete
function tables and generates equations for qualified calls into them. Ordinary
Lean module imports retain their public headers through Lean's persistent
environment. Headers select existing declarations, not arbitrary executable
Lean primitives. The [client examples](../../Examples/Language/Imports.lean) reuse
the original factorial and two-buffer composition proofs, then import that client
again. Each imported family exposes `P.imports.Library.map` and
`P.imports.Library.embedding`, using the family spelling in the `importing`
clause. These are source declarations, independent of the RAM backend.

`FunctionTotal.renameCalls` reuses a library's correctness contract through its
actual-body embedding. The separate
[resource contract rules](../../Complexity/Computability/Ram/Compiler/Language/Linking/Verification.lean)
provide `FunctionRealizable.renameCalls` and `FunctionCostBound.renameCalls`.
They transport dependent argument predicates internally, retaining the same
word width, call-nesting capacity and bound. Their justification proves that
lowering commutes with call relocation, including the inferred local frame,
and preserves exact execution counts in both directions. It does not infer
cost equality merely from equal mathematical results.

The [compiled client](../../Examples/Language/ImportsCompiled.lean) applies these
rules to the imported recursive factorial, then uses the existing structural
tactics to prove its caller and real halted invocation. The recursive library
proof is not reopened. The caller's additional call and nesting are counted;
code and stack capacity still refer to the complete target program.

The [connection-layer tactics](../../Complexity/Computability/Ram/Compiler/Language/Linking/Tactic.lean)
accept `via P.imports.Library.embedding` after their supplied contracts. This
applies the proved transport rules before the existing structural tactic, so
callers can pass original library theorems without local transport wrappers.
`ram_source_call using resource, specification via embedding` consumes one
call's contracts and stops at the next call. The
[effectful imported client](../../Examples/Language/ImportsTraversalCompiled.lean)
uses distinct contents contracts for two calls to the same traversal. The first
call's actual frame supplies the second input; the final runner retains both
mapped arrays and the outside-both frame in one represented heap. Its bound
reuses the original two-call bound via the proved equality of call overhead.
Routine consequences of supplied frames are automated; contracts and separation
facts are not discovered. The author still selects the contents and supplies the
mathematical separation argument.

### Current surface and intended traversal extension

The [typed frontend](../../Complexity/Language/Syntax.lean) accepts ordinary typed
headers and `do` bodies through the recommended default `source_program` entry.
The existing scalar example uses that same entry:

```lean
source_program Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if limit ≥ next then
      result := next
    return result
```

The [existing scalar consumer](../../Examples/Language/Scalar.lean) uses this
declaration and retains its mathematical minimum specification. The declaration
exports signatures, function identifiers and bodies, the shared program, and
native curried scalar functions. `Implementation.boundedIncrement_model n limit` has
type `Nat`; its minimum theorem uses the native definition, the increment
equation and ordinary Nat facts. The generated source action retains the independent
source observation, `_action_eq_native` proves its encoded native result and
exactly unchanged heap, and `_total` supplies its total source contract.
No second implementation proof or manual heap conversion is required.
In the recommended default layout, `P.f`/`P.f_eq` expose the actual
`ExceptT Fault (StateT Heap Part)` action and its one-step equation. An available
checked total model is named `P.f_model`; otherwise correctness uses a contract
of the same action. Native execution and the compiled RAM runner have different
runtimes; function equality neither sets an instruction price nor hides
intermediate work.
All function signatures are collected before lowering the bodies, so named
calls refer to the same source program rather than arbitrary host callbacks.
A named function returning `Unit` can appear directly as a statement; other
results require an explicit binding. The source call still executes, catches
the callee's return at its own boundary and passes its actual heap to the next
statement. No dummy return word or host callback is introduced.
The available surface also accepts `Buffer Nat` and `Buffer Bool`, their length,
`let x ← xs.get i`, `xs.set i x`, `let ys ← xs.slice offset length` and
`let ys ← Buffer.alloc length initial`.
These operations use the actual current shared heap. `let mut`, `x := expression`
and `x ← action` update existing typed locals; the latter reuses the same real
calls, reads and slices. An immutable nearest binding cannot be bypassed to
assign an outer mutable binding with the same name. The native equation uses
Lean's own mutable `do` and branch joins, not a second environment monad.
Surface `while` generates observations and equations for the actual parsed
guard and body, together with `variant_spec` and `wellFounded_spec`. General
proof automation remains unfinished. The buffer consumer separately
checks its source specification and the compiled invocation of that declaration.

Assignments also cover borrowed descriptors: changing a local handle does not
copy or change the referenced heap object. The compiler proves contiguous
fields and distinct live-variable slots for generated layouts, then reuses a
shared update correspondence. Buffer self-assignment is a safe sequential copy,
not an implicit snapshot or an extra no-alias requirement. Its real moves are
still charged. Ordinary source proofs never supply these layout arguments.

The checked [traversal](../../Examples/Language/Traversal.lean) writes its
read/helper/branch/write loop as `for i in [:xs.length]`. Its mathematical proof
uses native `Array.mapIdx`, `Array.set` and `Array.map` facts. Separate
`guard_contract` and `body_contract` theorems supply the same actual iteration
facts to `variant_contract`; no nested round triple or private execution adapter
is needed. A generated `spec` applies the chosen loop contract directly in native
`mvcgen`. The library restores fixed lexical captures and propagates control;
the author supplies the prefix invariant, descent and actual heap-frame facts.

The [compiled traversal](../../Examples/Language/TraversalCompiled.lean) reuses
those contracts through `StmtCostBound.while_contract_fixed` and
`RealizationWP.while_contract_fixed_of_total`. The library obtains their
postconditions from the actual guard/body executions. The cost proof supplies
potential inequalities; the realization proof supplies finite-word ranges and
reuses successful source termination, with no second decreasing argument.
Uniform guard/body and function-wrapper budgets are now inferred by the existing
cost solver and reused by direct, two-call and imported clients.
`ram_source_locals Implementation.boundedMap_loop1` replaces repeated capture
coordinate rewrites in the connection-layer consumer. It can act on one
hypothesis with `at h`, on the target, or on both, and uses only the selected
loop's registered coordinate and encoding equations. Named-loop resource tactics select the generated views and perform
source-totality conversion for the existing traversal. General allocating-loop
and potential interfaces still need further ordinary-argument composition. The mathematical invariant, actual
word ranges and potential inequalities remain author obligations.

The source and RAM results retain `xs.PreservesOutside initial final`: initially
valid disjoint views keep their contents, including slices of one shared object.
No global no-aliasing rule or unchanged-heap assumption replaces these facts.
The shared `BlockSpec.mono` consequence rule reuses native WP monotonicity while
keeping the initial condition available to mathematical postcondition reasoning.

The [recursive factorial](../../Examples/Language/Factorial.lean) makes a real
source self-call on `n - 1`. Its native theorem is
`Implementation.factorial n = Nat.factorial n`, proved by ordinary `Nat`
induction. The declaration supplies one `termination_by n` proof using
`simp_wf`, `simp_all +zetaDelta` and `omega`; generated correspondence and the
total contract establish the same source result and preservation of every
initial heap without a second author-written induction.
The same file's `Iterative.factorial` uses a finite `for` and mutable accumulator.
Its native equality proof converts the generated iteration to a fold and uses
mathlib's factorial product theorem. `Iterative.factorial_total` is then a direct
consequence of the generated source contract. This native proof does not itself
provide a RAM instruction bound for the iterative algorithm; the following
compiled consumer is the separate recursive declaration.
The [compiled factorial](../../Examples/Language/FactorialCompiled.lean) reuses that
source theorem unchanged. Separate induction uses `ram_source_realize (input)`
with the recursive contracts to prove that `n! < 2^w` bounds intermediate values
and that `n` nested calls suffice, without manual argument-environment or
statement-goal conversion. A second,
independent induction composes the actual primitive and recursive-call charges.
`ram_source_cost (input)` opens ordinary parameters instead of manual `Env`
unpacking; its supplied induction hypothesis handles the recursive call and the
structural pass selects the known base/successor branch. The author still supplies
the induction and arithmetic proof, not an inferred recurrence. The resulting
runner theorem retains code capacity and stack space for the outer call plus
those `n` recursive levels. Its bound is linear in the numeric argument `n`
in the word-RAM instruction model, not in binary input length or arbitrary-precision
multiplication cost. This is the first self-recursive source-to-runner consumer,
not yet a use of the generic mutual-recursion contract rule or an effectful
recursive program.

The core's `Stmt.while guard body` uses a Boolean-producing statement block as
its guard. Every iteration runs that block in the current state and passes its
actual final locals and heap to the body. A false guard exits in that updated
state. Guard fallthrough is a missing-return fault, not a false Boolean; a body
return exits the enclosing function. The source `while_wellFounded` rule asks
for descent only after a complete normally returning guard/body cycle.

The frontend exposes this through observations of the actual parsed blocks,
with ordinary named locals and proved equations for the guard and body. A
lossless change from typed environments to ordinary tuples is a proof view,
not a second algorithm or a source-level product implementation. Merely adding
an opaque loop alias, exposing `Env` to authors, or emitting Lean's partial
native `while` does not complete the interface. Guard normalization must remain
inside the loop, and returning a guard value must retain its updated locals.

```text
program transform (xs : Buffer Nat) (limit : Nat) : Unit := do
  for i in [0 : xs.size] do
    let x <- xs.get i
    let y <- increment x
    if y <= limit then
      xs.set i y
    else
      xs.set i limit
```

The behavior theorem says that final contents equal
`input.map (fun x => min (x + 1) limit)`, with the appropriate outside-buffer
frame. Its invariant describes the transformed prefix and untouched suffix.
It does not assert equality with a pre-proved whole-function RAM template.

The cost proof uses the same traversal, helper-call cost and branch/store
rules. A source-level representation argument establishes that each actual
intermediate `x + 1` fits the selected word backend; a small final result alone
does not establish that.

## Structured values and remaining language scope

**Status:** first-order calls, while, recursion and the first structured-value
layer are implemented. Native Lean `Prod` and `Option` values now pass through
constructors, projections, assignment, real matching, calls, returns and imports.
Their source contracts, word ranges, actual lowering and instruction counts use
the same execution. The frontend supports nested product patterns
and `_` in immutable bindings, including `let (x, y) ← call` and `some (x, y)`
branches. The right-hand side runs once; projections and copies are real generated
operations. This does not implement general algebraic patterns, sums or recursive
data representations. The revised structured consumer's source and actual RAM
theorems are checked together with the whole library.

The new native-structure path is separately checked in
[`Scalar`](../../Examples/Language/Scalar.lean) and
[`ScalarCompiled`](../../Examples/Language/ScalarCompiled.lean). A registered
ordinary structure is constructed, passed to a source callee, returned and
projected; that callee imports the existing scalar helper. Its mathematical
proof only reuses the helper's ordinary minimum equation. Generated native/core
correspondence and total contracts feed the existing range and cost automation,
and the final theorem describes the same halted RAM result. Reconstruction of
raw scalar layouts is generated and checked once at the connection boundary,
not written by the algorithm author or installed as an uncharged operation.
This does not extend reconstruction to arbitrary partial representations such
as bounded subtypes. This scalar reconstruction path handles direct scalar/scalar-product fields.
The default represented entry separately supports array-valued records and
heap-indexed contracts; it does not turn those observations into an `Equiv`.
General dependent records and richer reconstruction remain open.

`StructuredRange.sum` additionally keeps a native structure as a mutable
accumulator across actual helper calls inside a finite range, including dynamic
positive stride and a helper call before entry. Its ordinary fold/sum theorem
and generated total source contract are checked on 0v0. The connection layer
transports native and raw loop coordinates through checked equivalences;
algorithm authors do not supply encode/decode lemmas or a second loop proof.
Its generated native guard/body equations now take one captures tuple, with
endpoint/stride selectors derived from the actual range metadata. The shared
[`while_range_encoded`](../../Complexity/Computability/Ram/Compiler/Language/CostBound/Range.lean)
rule supplies round-count descent and normal/early-return accounting using
the existing compiler costs and `Std.Legacy.Range.size`. The complete function
body has an inferred bound in its ordinary start/stop/step parameters, independent
of the initial structure and heap. `structuredRangeSumBodyBound_eq` exposes it
as a fixed per-round charge times the ordinary range length plus fixed overhead;
both constants follow from the same compiler proof. Its consumer no longer builds private block
contracts or guesses captured-variable positions. The checked shared
[`RealizationWP.while_range_encoded_invariant`](../../Complexity/Computability/Ram/Compiler/Language/Realization/Range.lean)
also supplies finite-range termination while retaining the author's mathematical
invariant at normal exit. The dedicated `structured_range_sum_execute_le`
connects the same ordinary result and budget to an actual halted invocation,
including outer call/return/halt. Its extra word conditions cover the final sum,
last actual cursor and computed stride, even for empty ranges; the launch retains
input, code and stack conditions. The shared
[`ram_source_locals`](../../Complexity/Computability/Ram/Compiler/Language/LocalsTactic.lean)
pass selects the loop's registered view, endpoint and structure-encoding equations
from its namespace. Standard tactic locations restrict which hypotheses or target
are normalized; callee bodies, mathematical invariants and cost functions stay
closed. This removes repeated coordinate lemma lists in the structured range
and mutable traversal consumers. The traversal's named-loop resource tactics
also select capture views and fixed-capture frames from its existing contracts.
The structured range uses its separate encoded-range rules. Further resource
composition remains open; it must not add another per-program termination or
register proof.

The existing multi-field ABI concatenates product fields and places an option
tag before its fixed payload. `none` has canonical zero padding, not a default
buffer; only the selected `some` branch receives a payload. Copying and matching
have actual emitted costs. Recursive rootedness preserves the existing aliasing
and scratch-escape conditions even when borrowed views are nested in a tuple or
option. Mutable buffer cells remain scalar; this adds neither a new allocator nor a
global inverse of the buffer encoding.

The [complete consumer](../../Examples/Language/OptionalBufferCompiled.lean) imports
a pure helper returning `Option (Nat × Nat)`, constructs a full borrowed slice,
and returns `Nat × Option (Buffer Nat)` through another imported call. Its client
matches that actual result, reads and increments the first cell only when present,
and returns the structure. Ordinary array contents and frame contracts connect to
the real RAM result, four return words and a compiler-derived instruction bound.
The public execution theorem states the mathematical postcondition and time bound;
physical encoding consequences are separate projections of that same result.

Effectful functions already share a typed table supporting different signatures
and mutual calls; the pure native-function frontend has the narrower restriction
described in the [function-proof milestone](Verification.md#function-proof-milestone).
Explicit positive range steps share the native range correspondence, including
a dynamic `k + 1` consumer. The bounds and stride are
frozen once. The current generated proof must establish positivity from the
expression; a general user-supplied proof parameter is not yet accepted. The
RAM range condition includes the last increment actually executed, which may
exceed the stop value. Pure general `while` and source `break/continue` remain
open. Their semantics and proof/cost interfaces must be supplied, not inferred
from existing effectful loops or ordinary function return.

Then add the pattern/recursion and collection interfaces justified by actual
algorithms, reusing upstream data types as mathematical views. Structural
recursion over a collection requires a real representation and operations;
adding a `List` type name does not provide them. Higher-order notation may use
proved static specialization before dynamic closures are considered.

Use existing consumers to select the next missing operation or representation.
Reuse old implementations' mathematical lemmas through the connection layer;
do not create an algorithm catalog or call old register-level examples
high-level programs merely because their theorem names are accessible.
