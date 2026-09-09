# Design

The [roadmap](ROADMAP.md) sets development priorities, including the unresolved
total-function interface and memory-lifetime decisions. The
[cross-prover research report](DESIGN_RESEARCH.md) motivates complementary pure
and mutable proof interfaces over shared contracts, with explicit termination,
allocation and target-cost boundaries. The
[high-level language design](HIGH_LEVEL_LANGUAGE.md) specifies the next
architecture: an independently interpreted typed core, source-level proofs and
automatically checked lowering to the existing RAM backend. Its independent
core and whole-function proof transfer are implemented separately. The
`source_program` frontend targets that independent core; `ram_def` remains the
named register-IR interface. A private return flag
avoids copying continuations; its exact static code-size formulas retain real
callee-frame expansion. Realized scalar source costs now correspond to actual
measured execution, with conditional source bounds and outer-call accounting.
Borrowed buffers, mutable locals and typed effectful-guard loops have source
rules and compiler connections. The semantic Std.Do adapter reuses strict Part
and native state transformers. Named while syntax and ordinary-local variant
rules exist; complete loop-proof automation, native total-function generation,
richer data and allocation remain unfinished.

The sections below document the existing implementation and the semantic
boundaries that its reuse must preserve. Here, `Source` means the current
register-based `Stmt/Func` language, not the proposed high-level core.
The [backend manual](https://vvauted.github.io/Complexity/ComplexityDocs/Backend.html)
describes the current machine and compiler interfaces.

These interfaces remain an active development surface for compiler maintainers
and low-level primitive authors. The high-level language removes register-proof
obligations from algorithm clients, not from the library's research agenda.
Reusable state/frame, call/return, control-flow and cost proofs, including their
automation and source-directed navigation, advance alongside the new language.
The roadmap gives both tracks explicit consumers and completion criteria.

## Current implementation: one program, several proof views

The current executable source is a fixed first-order program, with structured
control flow, named functions and recursive calls. The existing compiler lowers
it to word-RAM instructions. This compilation chain is reused as the backend
for the new language. One high-level program with an independent semantics and
a compiled representation is not two manually maintained algorithms. The
current named elaborator directly produces `Stmt/Func`; body equations and
source metadata alone do not prove correspondence with an independent
high-level semantics.

Intermediate functions are the primary programming interface. Their arguments,
return values and shared-data effects must be available without a stream-based
`main`. Reading and writing external input belong to an optional outer driver.
Parameter binding and result observations are derived from the same source
declaration, not restated by each caller. Named declarations generate `eval`,
`bodyTime`, `run`, `runTotal`, `apply` and `applyState` entries with the declared typed
parameters, followed by heap capacity and caller state. The last three additionally
require a normal-halt proof. They reuse the existing semantics and runner; they do not fill
in a reference result, a cost formula or a correctness proof.

Source `include priorDeclaration as Alias;` reuses earlier `ram_def` implementations
and their stored parameter and result signatures. Function tables are combined with the existing
`Program.link` relocation; new functions are appended and qualified source calls
resolve in that final table. Generated index maps and embeddings transport the old
contracts instead of duplicating implementation proofs. These are static source
imports, not host callbacks, runtime module loading or arbitrary Lean compilation.
All six generated observation/run interfaces are available under imported aliases.
Stored signatures survive further imports; bare term quotations cannot resolve includes.

Declarations also generate a dedicated binding simp set for argument fields,
lookup and static arity/frame/result counts. Correctness and cost tactics reuse
that one set. Function bodies, return expressions and representation theorems
are not registered, so an implementation remains opaque until explicitly opened.
Source Boolean literals do not reserve the host Lean identifiers `true` and `false`.

Word, borrowed-array and `Unit` results have one, two and zero fields. All return
expressions are evaluated in the same final callee state before restoring caller
registers. Result arity is checked; receipt updates destinations in order.
Scoped `call f(...);` and `let _ ← call f(...);` omit the source result binding.
Non-`Unit` fields still receive fresh anonymous destinations in the inferred frame;
a genuine `Unit` call has none. Both execute the body, effects and calling convention.
Raw `ram%` and `ram_stmt%` quotations do not infer a frame and retain explicit destinations.

The generic execution state retains input and output fields because functions
may have effects. Merely carrying those fields does not execute stream operations.
A pure function's contract must establish independence from their initial contents
and preservation on return; selecting an empty stream alone would not prove this.

A functional specification may be a relation, an ordinary Lean function or a
native `StateM` computation. These are proof views. A sorting specification need
not implement another sorting algorithm, and a loop need not be translated into
a total pure function before its termination can be proved.

`TypedFunctionContract` is a representation view of that same `FunctionExec`,
using typed parameters and `Word`, `ArrayRef` or `Unit` results. Its encoder
describes the declaration's actual fields; it is not a second program or a loader.
The body rule decodes the callee's real results, and the call rule passes the
typed value and shared effects to its continuation. A fixed-input adapter reuses
existing raw contracts and independent time rules without assuming that arbitrary
raw arguments represent valid typed inputs.
For a subsequent source call, `call_seq_typed_at` combines this contract with an
independently supplied callee-time theorem and keeps the typed result in the
time continuation. Its bound can depend on that value and shared state; slice
uses the returned reference's length. The adapter reuses the original call rule,
not a second cost semantics or a default-valued raw-field decoder.
The restored variant presents the same shared effects with caller bindings
already restored. Its default remaining-reserve variant subtracts the complete
proved call bound only after proving it fits. This removes intermediate reserve
choices, not the overall recurrence or domain obligations. Explicit bounds
depending on the returned value and shared state remain available.

Representation predicates relate mathematical values to visible machine state.
Use mathlib equivalences when information is preserved, and relations when a
view forgets information. An entire heap is not in bijection with one observed
list. Mathematical functions used in specifications are not executable primitives.

## Behavior first, cost second

Safe total correctness establishes an actual terminating execution without a
proposed time bound. A separate conditional time theorem bounds that execution.
Publishing and composing reusable implementations should preserve this separation.

The returned value and execution count are observations of the program, not
fields filled in by its correctness proof. Specifications and asymptotic bounds
describe those observations. An ordinary functional view must therefore come
with its connection to that implementation; declaring a mathematical reference
function alone does not make it the executable program.

`Func.eval` and `Func.bodyTime` provide proof-level observations using mathlib's
`Part`. Their domains come from safe executions, and determinism proves that
the observed result and count belong to the same invocation. Classical choice
selects only that uniquely determined observation. It does not install a
reference algorithm or a proposed cost as the program's meaning. These views
are noncomputable; executable application remains on the verified runtime path.
Heap capacity can affect the domain, and shared entry state cannot be hidden
without proving the relevant result and cost independence.

Generated `eval` uses the single shared `Func.evalTyped` projection. Its decoding
preserves all returned fields; the inverse encoding/decoding laws reuse standard
list facts. The projection changes the mathematical view, not the chosen execution.

The executable function adapter uses the existing compiler and machine runner.
It places runtime arguments in parameter registers, launches a fixed call-and-halt
sequence and returns the value separately from stream output. Preloading shared
state is explicit; no loader or host-side data conversion is silently included.
The measured call includes argument evaluation, frame handling, the body, return
and halt. `Function.runUntil` has no operational limit and uses the existing
machine step until a stopping state; `Function.run` retains a limit for exploration.
Both relate to the same finite traces. The unbounded runner's logical bottom is
not an executable divergence test. Source shared memory is related only to visible
target heap cells, not to the private stack left behind by the call.

Ordinary executable application uses this same runtime path. `Function.Halts`
asserts that the actual `runUntil` returns `some result` with reason `halted`;
merely returning an optional result would also admit faults. `runTotal` applies
`Option.get` to that real output, and raw `apply` projects the returned fields. Neither
uses `Part.get` or extracts an answer from the specification. The `Prop` proof
is erased at runtime and can follow from safe source termination before any time
bound is supplied. The full result still carries the actual transition count,
with its equation proved independently about that same run.

These are executable ordinary Lean wrappers around declared RAM functions,
not a compiler for arbitrary Lean definitions. They support `#eval`; ordinary
kernel reduction of the partial-fixed-point runner is not their correctness
interface. Value equations come from the execution bridges. Fixed word width,
sufficient capacity and represented preloaded data remain genuine conditions.
Projecting the returned word alone does not establish preservation of shared state.

Generated `apply` and `applyState` decode the declared fields without default words;
`applyState` pairs that typed value with reusable source shared state from the same run.
`returnState` keeps caller registers and out-of-heap entry memory, takes actual
target memory below the heap boundary, and retains actual I/O. Safe execution
proves this projection equals the source final state; target stack cells are not
shared data. Existing contract postconditions transfer through `applyState_spec`.
Its typed counterpart is `applyStateTyped_spec`; `applyTyped_spec` additionally
projects a proved property of the returned value. This hides state only from the
chosen conclusion, not from execution or its correctness premises. It does not
assert that an effectful program is pure.
Passing this state between host-level applications does not itself compile their
composition into one RAM program or supply a combined RAM-cost theorem.
Source composition is separate: including copy and sum and calling them inside a
new function produces one compiled invocation. Its cost proof reuses independent
callee bounds and counts the actual inner and outer calling conventions.

Source-facing time rules start at the actual parameter-bound state and infer the
call expressions and destination from the source body. A supplied correctness
contract exposes the returned value, shared-state postcondition and preserved
caller locals to the rest of the independent time proof. A remaining bound is
proved against that continuation, not passed to the implementation as fuel.
Generated parameter/local-count equations and proved call-length formulas reduce
overhead without reopening callee bodies. This automation does not choose the
mathematical bounds, infer invariants or remove representation and safety premises.
`ram_time_vc` also advances leading assignments and skips, reassociating sequences
as necessary. It carries the actual updated state and subtracts only proved
compiled assignment costs from the remaining proof bound, stopping at calls and
loops. A descriptor initializer therefore cannot disappear from a call's cost proof.

An `array` parameter is a typed by-value pair of words, not a newly allocated
descriptor. Its base and length are passed by the same call compiler as scalar
arguments. `ArrayRef.Rep` relates existing heap contents to a list; changing this
mathematical view or forming host-side subarray metadata performs no RAM copy.
Inside source code, `let window : array := subslice(xs, offset, count)` instead
executes two fresh local assignments, including word addition for the shifted
base. `let other : array := window` copies the two descriptor words, not heap cells;
`array(base, length)` constructs a handle from ordinary word expressions.
All such assignments and their local-frame effects have the compiler's real cost.

Array initializers and typed array call arguments accept those forms, but they
are not general eager array expressions. `subslice` starts from an already bound
handle, optionally parenthesized; bind constructed or nested handles first. It
sets the requested length without runtime containment checks, truncation or
allocation. `ArrayRef.Rep.subslice` separately proves the `List.drop`/`List.take`
view under containment, and operation contracts retain address-range premises.
Immutable bindings prevent descriptor-field assignment while still allowing
writes through their addresses; `let mut` permits updating `base` and `length`.
Aliases share the underlying heap, with no ownership or disjointness guarantee.
Array-valued returns use these same two actual fields and may be passed to another
compiled source call. Allocated-array construction and richer value types still
need implementation and cost interfaces; representation predicates do not supply them.

The reference-level copy contract still encodes only source base, destination
base and source length. The destination length is constrained by its input
representation and equal-length premise, not decoded from these three words;
no encoder injectivity is assumed. Complete represented arrays are returned to
the proof continuation at the same actual endpoint. The raw API remains available.

Heap and call-depth capacities are safety premises, not instruction budgets.
Output-size guarantees support subsequent operations. Time analysis may reuse
these facts and functional invariants, but correctness must not depend on the
particular time estimate chosen later.

The source language does not accept a pricing table, arbitrary host-language
callbacks or unchecked ticks. Operation costs come from proved executions of
emitted instructions, including argument evaluation, frame save/restore and
control-flow overhead.

The read-only array fold shares one cursor, termination and framing proof for
expression updates and fixed function calls. A call-based step uses a contract
of the actual callee to establish its mathematical `List.foldl` update and
unchanged shared state. Its separate exact-count rule adds the real call and
loop instructions to a proved constant callee-body count. That exact-count rule
neither compiles arbitrary Lean callbacks nor handles varying helper cost.
A separate uniform upper-bound rule accepts `FunctionTimeBound` for each actual
two-argument helper call, without requiring an exact count or helper totality.
It bounds completed traversals; existence still comes from independent correctness.
The data-dependent rule sums `C accumulator element` at the actual fold prefixes.
It additionally uses a separate read-only helper contract to identify the
returned accumulator and preserve unread elements. Accumulator invariants and
admitted element domains are explicit; the shared guarded traversal requires
helper correctness only for iterations whose guard is true, not at the empty
endpoint. The actual factorial adapter exercises a varying helper bound without
requiring all word inputs to fit a fixed recursion depth.

`TimeExact` states an equality about every completed measured execution. Its
source-compositional rules reuse compiled straight-line lengths, branches and
calls; no new execution relation or cost annotation is introduced. A single
cost induction can supply both an upper bound and the count of a separately
proved safe execution. Conditional equalities and bounds are not automatically
monotone in safety capacities: an insufficient capacity can make them vacuous.
At the executable boundary, `ram_run_eq` and `ram_run_bound` apply existing
runner bridges and normalize their proved outer-call overhead. They do not
derive a body-time theorem from functional correctness or discharge stack safety.

Scoped `for x in xs` lowers to the same statements: two fresh cursor locals copy
the descriptor, and a third local receives each actual element load. The source
element binding is immutable and does not escape the body. Generated control
code leaves the original descriptor alone; array contents are read at each
visit, not snapshotted. The generic AST helper retains its actual sequential
evaluation order, while frontend freshness makes the copied descriptor stable.
All copies, bindings and enlarged call frames retain their compiler-derived cost.
The indexed form `for i, x in xs` adds a fresh index initialized to zero and
incremented after each body. Both names are immutable and confined to that body.
The array handle is resolved before either name shadows an outer binding;
the generated increment refers to the originally allocated index slot even if
the body shadows `i` again. Its real assignment is appended to the same
right-associated statement sequence. Map's indexed source is definitionally
the same function as its explicit-counter implementation, with identical costs.

For the single-array scalar-call pattern, a function rule reads the body/result
equations to infer those slots, reusing the same traversal and callee contract.
The expression-update rule uses the same generated equations for an array-first
function with additional word parameters. It maintains the entire
`array.args ++ captures` parameter prefix, so sum and count share traversal,
termination and framing without a client-written cursor or target invariant.
The client still proves the actual expression's read safety and mathematical
evaluation using those parameter equalities. A separate measured rule counts
the compiled expression and traversal instructions in that same invocation.
These rules cover one initialized scalar accumulator with an expression update
or the supported fixed helper call. General `TotalWP.forIn` instead accepts an
arbitrary loop-head invariant and a contract for the real loaded-body entry and
advanced-body endpoint. It imposes no whole-heap or I/O preservation condition.
Its count-preservation premise concerns the body's own loaded entry; the element
and remaining locals must be distinct to connect this to the loop-head count.
The invariant before loading is not automatically available after loading.

`TotalWP.forIn_indexed` keeps the fixed forward cursor trajectory and remaining
count inside the shared proof. Its payload is indexed by an ordinary natural
iteration number; clients need not repeat private-pointer/count arithmetic or
the exit-index proof. The body starts with the real current-heap load and proves
the next payload after the actual cursor assignments. Its semantic preservation
premise allows cursor writes followed by restoration.
For payloads stable under `State.LocalFrame {pointer, remaining}`,
`forIn_indexed_of_frame` handles their transport through both setup and advance.
Map's body now proves its own endpoint payload and supplies this frame stability
once, retaining mathematical contents, the real index and store/frame reasoning.
Only the generated cursor assignments are framed as shared-state preserving;
the body may still mutate memory and I/O. Stability is proved, not inferred,
and the interface still does not provide declaration-level named invariants or
strengthen the endpoint address requirement.

The separate uniform `TimeBound.forIn` bounds completed traversals without body
totality. It reuses the existing linear-loop rule and includes the load, both
cursor updates, guards and setup. The general rules take three register roles,
not a dummy scalar accumulator. They do not yet provide a declaration-level
mathematical adapter for arbitrary mutable bodies or an early-exit construct.
The in-place map operation uses that rule with an updated-prefix/unread-suffix
invariant. Its real helper call and indexed store produce `List.map` contents,
preserving outside-array memory and I/O. Only the original elements need the
helper's budget-free contract; the separate uniform bound covers completed
one-word helper invocations. The body proof sequences the existing call WP,
array-store contract and assignment WP directly into the next list invariant;
it does not first construct an explicit whole-body state. The time proof
composes the call with its uniformly bounded store/assignment tail using
`TimeBound.seq_const`, which requires no totality premise. No snapshot, runtime
callback or heap loader is introduced. The named square-map instance is definitionally the same operation
with its helper index resolved by the existing static import.

That focused operation is not a general named-invariant elaborator. The source
template still fixes its private local layout internally, and arbitrary mutable
loop proofs remain source-state proofs. An effectful helper that changes other
data requires a stronger ordered representation relation; pure `List.map` does
not justify discarding those effects or transferring a cost between loop orders.

The named lowering retains intermediate proof sites separately from the
executable definitions. Each site records its lexical scopes, original source
location, actual emitted fragments and child locations; block anchors also
retain empty scopes. Generated index setup and tails are distinguished from
user statements, not deleted. An inner shadowed name therefore cannot redirect
the captured index update. Source immutability is not a proof that a loop-local
value remains constant across iterations.
Parent and child fragments overlap; the flat site array is not an execution
trace. A driver descends through the hierarchy instead of concatenating or
charging every recorded fragment.

The initialization proof driver consumes these sites in the current lexical block's order,
advancing only complete assignment/skip source statements. An array descriptor
is exposed only after both real field assignments. It uses the actual goal's
elaborated expressions; retained source terms are never elaborated again in a
different Lean scope. The two proof modes share navigation and typed observations,
not execution rules: total correctness retains unresolved read safety, while
conditional time bounds retain affordability and charge emitted instructions.
Naming the resulting state and its `Word`/`ArrayRef` locals adds proof-only views,
not executable conversions, a loader or assumptions about arbitrary heap effects.

Known-branch entry uses the same block traversal. A code goal can retain its
declaration, block path and next source position in Lean expression metadata;
entry checks the statement at that exact path in the supplied actual function.
This is neither an AST search nor another stored execution. Proved sequence and
conditional rules retain parent continuations, guard evaluation and generated
jumps. A missing `else` consumes its actual skip, without inventing a child scope.
These are proof rearrangements over counted executions, not edits to the compiled program.
Completing a child restores the parent scope; array locals still require both
field assignments before becoming visible.

The generated Lean lets are snapshots of values at that point. Existing typed
call rules can use their binding equations and pass the lets into continuations.
They do not maintain the source cursor or refresh mutable bindings. A call's
actual postcondition, not these snapshots, justifies any changed heap assertion.

General source-directed proof elaboration remains unfinished. The sites are not
new correctness certificates. Extending the driver must follow the actual WP
decomposition and give a lexical cursor only to code continuations. Expressions
and effects come from that proof goal, not from reinterpreting stored source
syntax. In particular, source locations do not justify transporting a heap
representation across a call. Imported bodies are proved at their original
declaration and transported through the existing semantic embedding.
The persistent lookup currently registers local function bodies, not `main`
or relocated imported aliases. Missing metadata must not mean an empty body.

Local binding adapters can use `State.LocalFrame` to transport a collection of
unchanged parameters through those actual state updates. Its register relation
is mathlib's `Set.EqOn`; composition takes the union of allowed endpoint changes.
It also requires unchanged shared memory and I/O, so it is not a general effect
system or an execution trace. Parameter initialization replaces the whole local
environment: subsequent local assignments are compared with `entry.enter args`,
not the original caller. `restore_eq_of_shared` restores caller state from the
three shared-state equalities without assumptions on discarded callee locals.
Read safety, mathematical evaluation and compiler-derived costs remain separate
obligations. Individual unchanged-register reads need not use the collection rule.

For effectful bodies, `Stmt.writtenRegs` conservatively tracks only caller-local
destinations. The existing execution preserves locals outside that set, while
memory and streams may change. Calls contribute their result destinations, not
callee-private assignments. This can discharge traversal count preservation;
it is not a heap frame or a requirement that all legal bodies satisfy static
exclusion. Writing and restoring a local still admits a direct semantic proof.

`TotalWP.assign_value` names the evaluated word at one assignment and passes its
evaluation equality to the continuation. `ram_total_bind` applies this rule to
an assignment or a sequence beginning with one. It simplifies only explicitly
supplied definitions first, closes read safety only when proved, and leaves the
continuation unsimplified. Search uses the name for its actual midpoint rather
than repeatedly expanding word arithmetic. This proof-local name does not export
a loop-scoped source variable, infer layouts, or bind an array's two fields as
one value. Naming an assignment does not remove its compiled cost.

## The current machine model

Words and addresses are finite bit vectors. Arithmetic has the specified modular
semantics; exact natural-number arithmetic requires no-overflow hypotheses.
Multiplication and division are primitives of this word-RAM model.

One executed transition costs one step. This is neither the runtime of the Lean
interpreter nor a claim about bit complexity. The optimized runner has a
correspondence theorem with the reference execution.

Address-space capacity, cumulative accessed addresses and peak live storage are
different resources. A new space claim needs its own observation of the same
execution, including allocation or reclamation if it refers to live heap.

## Complete claims

A problem fixes its encoding, admissible inputs, width policy and size measure
before an implementation is certified. Composition must preserve that original
domain and the actual intermediate representation.

Reading, initializing or converting data is runtime work when the implementation
performs it. A proof-only change of mathematical view is not a data conversion.
Preloaded-memory contracts state their entry state explicitly.

The compiler, representation and cost theorems connect to one fixed program
uniformly over legal inputs. Cross-model complexity claims additionally need a
costed simulation; payload-size arithmetic alone is not one.

## Reuse and scope

Reuse Lean, Std and mathlib definitions and theorems. Keep their pinned versions
consistent, and extend ordinary mathematical namespaces for generic results.
Backend-specific statements stay under the RAM topic.

The [literature notes](LITERATURE.md) explain the sources behind these choices.
They motivate the design; the guarantees are the theorems in this repository.
