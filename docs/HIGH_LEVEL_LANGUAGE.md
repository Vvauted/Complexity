# High-level language design

Status: `source_program (pure)` generates native total functions over scalars
and their products/options with checked source correspondence. Self-recursion,
acyclic calls and finite-range `for` are supported; general pure `while`, mutually
recursive pure families and buffers are not. Effectful declarations
retain their partial heap-action interface. Named `Buffer.alloc` has a checked
allocating-callee/using-caller path to RAM, including resource-import transport.
Scoped scratch reclamation now has a checked same-source runner and physical
workspace bound independent of repeated call count; see
[the implementation checklist](RECLAMATION_TODO.md). The
high-level programming/proof interface remains incomplete; the
[roadmap](ROADMAP.md) distinguishes its working foundations from planned APIs.

The [cross-prover research report](DESIGN_RESEARCH.md) supplies the rationale
for the next interface: one supported implementation, a common mathematical
contract layer, and complementary pure-equation and mutable-VCG proof modes.
Executable pure functions are implemented for the buffer-free subset; extending that
interface does not replace verification of genuinely effectful algorithms.

The independent scalar core now has
source correctness rules, generic whole-function lowering and proof transfer to
the existing executable RAM runner. Return-flag lowering avoids continuation
duplication and has exact static code-size formulas. A separate cost observation
of realized scalar executions now transfers source bounds to the actual runner,
including internal calls and the outer invocation overhead. The Lean-like
scalar `source_program` surface, independent `Part` observations, compositional
evaluation equations and a scoped strict Std.Do interpretation are now present.
Generated one-step function equations support ordinary mathematical correctness
proofs; shared structural rules compose separate cost bounds. Default declarations
expose noncomputable semantic actions; `(pure)` additionally generates executable
native functions and proves correspondence to those same source actions.
Generated contract equivalences hide argument-environment packing, and named
specification rules apply supplied contracts in native `mvcgen` proofs;
focused scalar tactics compose realization and uniform structural cost rules.
Source execution and function contracts carry typed locals and a shared heap;
their native monadic view retains the final heap on success and failure.
Borrowed-buffer length, reads, writes and slices now have source syntax and
semantics and checked whole-compiler behavior/cost connections. Mutable local
bindings and assignments use the same source state, native equations and lowering.
The typed core now includes effectful-guard loops and well-founded source rules.
The surface accepts `while` and generates named guard/body/loop equations,
normal-continuation proofs and termination rules over mutable locals and the heap.
The complete buffer traversal proof now gives its ordinary `Array.map` result,
preservation of disjoint views, termination, compiled invocation and independent
linear instruction bound.
A finite-range factorial also uses a generated native function: one accumulator
loop is proved equal to `Nat.factorial n` with ordinary fold/product identities.
Its total source contract follows from generated correspondence, not a second
termination or implementation proof. Factorial and the direct/composed/imported
compiled traversal modules exercise the finite-range and inferred-budget
interfaces; they pass on 0v0 together with the library, Examples and manual.
A self-recursive factorial proof uses ordinary induction and mathlib's
`Nat.factorial`; its compiled invocation now has a separate linear instruction
bound, subject to word-range and code/stack-capacity conditions. The
[roadmap](ROADMAP.md) records these boundaries and defines completion gates.
Typed program embeddings now preserve complete source observations, including
divergence and finite faults. Linking the existing traversal and recursive
factorial tables reuses their original native proofs without unfolding either
algorithm. The frontend now accepts `source_program P importing Library, Other where`
and qualified calls into those libraries. Added bodies use the combined table;
generated caller equations expose original library actions through proved
embeddings. An imported program can itself contain imports. Separate connection-layer
theorems now preserve realizability and exact compiled body counts through these
embeddings, including the actual callee frame and call overhead. Source action
equality alone is not the justification for those resource results.
Program sketches and proposed interfaces below are schematic, not a claim that
the complete language/API is available.

## 1. The abstraction boundary

Algorithm authors write one high-level program and prove ordinary mathematical
properties of that program. They do not prove a register program, even indirectly
through a per-algorithm adapter. RAM is an implementation and cost-model backend.

There are three distinct responsibilities:

| Author | Responsibilities |
| --- | --- |
| Algorithm author | Mathematical specification, invariant, termination argument, algorithmic bounds, and genuine input/alias/range conditions |
| Language/library author | Source-level verification rules, mathematical data views, operation contracts and their composition |
| Backend author | Representation, register allocation, calling convention, lowering correctness, capacity translation and instruction accounting |

Generated register correspondence, local freshness, receiver updates, frame
restoration and function-table relocation are discharged by shared compiler
proofs. They must not become user obligations when a new loop body is written.
Unsatisfied arithmetic or representation conditions are reported at the source
operation, not as an unexplained RAM state equality.

Backend authors are first-class library users too. Removing register proofs
from algorithm-author work means developing reusable compiler proofs, not
stopping low-level proof development. Maintain register/IR and machine-level
lemmas, composition rules and automation alongside this language, with direct
proof interfaces for new lowering cases and low-level primitives. Source-cursor
navigation can improve that workflow; its metadata is neither a semantic proof
nor a prerequisite for using the low-level rules.

### Reducing proof work at the abstraction boundary

Interface work starts with the program authors can express, not with
abbreviations for a backend theorem. Ordinary product patterns and bounded
`for` loops elaborate to the existing core. A pattern evaluates its
right-hand side once; a range retains its entry-time endpoints; iteration over
a borrowed buffer reads each cell from the current heap. These are semantic
requirements, not permission to replace mutation by an entry-time snapshot.
Native finite-range correspondence is proved separately from the effectful
surface lowering and exercised by the iterative factorial. The proof-experience
work now concerns hiding local-coordinate and contract conversions, not adding
another loop semantics.

Three kinds of mechanical work belong in the library:

1. **Local bookkeeping.** Generate the lossless local views, fixed-capture
   proofs, pattern scopes and return propagation. Public block contracts take
   ordinary parameters and mathematical pre/postconditions, without asking an
   author to reconstruct `Control`, `Env` or nested output tuples.
2. **Contract composition.** The author supplies guard and body contracts
   separately. A shared loop rule passes the actual post-guard state to the
   body, retains the complete round's starting state for descent, and handles
   false guards and early returns. Heap frames follow proved operation/callee
   facts, not a global no-aliasing assumption. The generated API must be used
   by the existing traversal, not merely accompanied by an equally long
   private adapter.
3. **Backend publication.** A shared boundary connects a mathematical result
   and independent resource argument to the same actual execution. Input
   layout, output observation and word-width policy belong to that boundary,
   not to each problem's solution. Mathematical correctness must not require
   a proposed instruction budget, and a conditional cost bound alone must not
   count as successful compiled execution.

Algorithmic invariants, genuine data/range assumptions and asymptotic analysis
remain mathematical proof obligations. Their established consequences should
be available to correctness, realizability and resource reasoning at the same
program point; opening a lower-level goal must not force a second proof of the
algorithm.

The benchmark exercise is deliberately statement-only: one fixed source
implementation must meet the mathematical answer relation and a uniform
word-instruction bound. A public logarithmic input-width rule may have a fixed
implementation overhead, but not an arbitrary input-dependent admissibility
predicate selected by the candidate. Preloaded calls remain explicitly distinct
from a complete input-stream loader. The top-tree work independently develops
mathematical clusters and decomposition rules; a cluster datatype is not yet a
balanced dynamic implementation or a RAM complexity theorem.

## 2. Decision: a typed core with independent semantics

Use a typed, first-order core language with a Lean-like programming surface.
The elaborator retains a typed program as the semantic object, then compiles it
to the existing `Ram.Source.Stmt/Func` intermediate representation.

```text
one high-level declaration
           |
       typed core
       /        \
source behavior  backend lowering + checked certificates
and source WP         |
       |         existing Stmt / Func
mathematical          |
proofs           existing verified RAM compiler
       \              |
        ----- execution and cost theorems
```

The core's execution is NOT defined as execution of its lowered RAM program.
It has values, lexical environments, function calls and an abstract heap, without
register numbers, RAM states, ABI fields or compiler call-depth parameters.

One program may have both an independent semantics and a compiled representation.
This is not maintaining two algorithms. The forbidden duplication is asking the
user to write a reference algorithm and a separate machine implementation, then
prove their correspondence for every new program.

Alternatives not selected:

- Extending source cursors over lowered WP goals alone. This improves backend
  tooling but does not supply an independent high-level meaning.
- Accepting arbitrary Lean `StateM` computations as executable primitives.
  Their types do not expose all computation, allocation or cost.
- Replacing the existing verified machine/compiler with a new backend, or
  implementing a complete compiler for arbitrary Lean terms.

The semantic boundary begins at the elaborated typed core, as ordinary Lean
reasoning begins with elaborated terms. We do not claim verification of the
text parser/elaborator itself. Generated terms and correspondence proofs are
kernel checked; a `body_eq := rfl` about the lowered term is not the required
source-to-target correspondence.

## 3. Programming model

Ordinary closed structures with direct scalar/scalar-product fields now have a
checked first native frontend path. `source_type` derives their encoding and
constructor/projection equations; one pure source declaration can construct,
pass, return and project them while calling an imported source helper. The
[`Scalar`](../Examples/Language/Scalar.lean) consumer proves the ordinary native
function equation and reuses generated `_refines` and `_total` contracts. Its
[`compiled consumer`](../Examples/Language/ScalarCompiled.lean) uses the shared
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
[`ram_source_locals`](../Complexity/Computability/Ram/Compiler/Language/LocalsTactic.lean)
pass normalizes that loop's local coordinates and registered structure encodings,
without a consumer-written list of view or projection lemmas. Ordinary-parameter
resource rules should still remove the remaining contract/view setup.

This structure pass does not yet support general loops, recursion, matching,
type parameters, dependent fields or nested/Option-valued structure fields.
The scalar frontend separately supports self-recursion. Raw-to-native
reconstruction is available only for supported
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
`none` requires an expected Option type or an explicit type annotation. Pure
mode permits recursively heap-handle-free products/options; hiding a borrowed
buffer or node reference inside either constructor does not make a function pure.
The current match syntax has explicit `none` and `some pattern` branches (in either
order). Immutable lets, call-result bindings and `some` payloads accept nested
product patterns and `_`. They evaluate the supplied expression or call once,
then project the used fields through actual source primitives. Duplicate binders
are rejected. General constructor matching and user-defined inductive types
are not implemented.

The [imported structured client](../Examples/Language/OptionalBuffer.lean) uses
a pure `Option (Nat × Nat)` helper and a library returning
`Nat × Option (Buffer Nat)`. Its ordinary array/frame contract and
[compiled result](../Examples/Language/OptionalBufferCompiled.lean) describe the
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

Effectful `for i in [:stop]` and `for i in [start:stop]` use half-open ranges
and unit steps, with an immutable iteration index. Endpoints retain their
entry values: a literal or lexically immutable local/length can be reused;
other expressions are captured once. `for x in xs` retains the entry buffer
view but reads each cell from the current heap, so earlier writes through an
alias are visible. Both forms elaborate to the existing while semantics;
an early return leaves the enclosing function. Explicit steps, `break` and
`continue` are not yet supported. The checked mutable traversal uses
the same generated loop-contract interface.

For `(pure)` declarations, finite ranges generate a native total iteration over
the same normalized body. A shared finite-iteration theorem connects it to the
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
program. The [source linker](../Complexity/Language/Linking/Basic.lean) now
provides signature-preserving call renaming and checked embeddings of actual
bodies. Its [observation theorem](../Complexity/Language/Linking/Eval.lean)
preserves the entire partial action, so existing mathematical contracts transfer
without re-proving recursion, loops or heap effects. The frontend's `importing`
clause now resolves previously declared source families, retains their complete
function tables and generates equations for qualified calls into them. Ordinary
Lean module imports retain their public headers through Lean's persistent
environment. Headers select existing declarations, not arbitrary executable
Lean primitives. The [client examples](../Examples/Language/Imports.lean) reuse
the original factorial and two-buffer composition proofs, then import that client
again. Each imported family exposes `P.imports.Library.map` and
`P.imports.Library.embedding`, using the family spelling in the `importing`
clause. These are source declarations, independent of the RAM backend.

`FunctionTotal.renameCalls` reuses a library's correctness contract through its
actual-body embedding. The separate
[resource contract rules](../Complexity/Computability/Ram/Compiler/Language/Linking/Verification.lean)
provide `FunctionRealizable.renameCalls` and `FunctionCostBound.renameCalls`.
They transport dependent argument predicates internally, retaining the same
word width, call-nesting capacity and bound. Their justification proves that
lowering commutes with call relocation, including the inferred local frame,
and preserves exact execution counts in both directions. It does not infer
cost equality merely from equal mathematical results.

The [compiled client](../Examples/Language/ImportsCompiled.lean) applies these
rules to the imported recursive factorial, then uses the existing structural
tactics to prove its caller and real halted invocation. The recursive library
proof is not reopened. The caller's additional call and nesting are counted;
code and stack capacity still refer to the complete target program.

The [connection-layer tactics](../Complexity/Computability/Ram/Compiler/Language/Linking/Tactic.lean)
accept `via P.imports.Library.embedding` after their supplied contracts. This
applies the proved transport rules before the existing structural tactic, so
callers can pass original library theorems without local transport wrappers.
`ram_source_call using resource, specification via embedding` consumes one
call's contracts and stops at the next call. The
[effectful imported client](../Examples/Language/ImportsTraversalCompiled.lean)
uses distinct contents contracts for two calls to the same traversal. The first
call's actual frame supplies the second input; the final runner retains both
mapped arrays and the outside-both frame in one represented heap. Its bound
reuses the original two-call bound via the proved equality of call overhead.
This is not automatic discovery of contracts or frame consequences: the author
still selects the contents and supplies the mathematical separation argument.

### Current surface and intended traversal extension

The [scalar frontend](../Complexity/Language/Syntax.lean) accepts ordinary typed
headers and `do` bodies; `(pure)` selects the checked native scalar interface:

```lean
source_program (pure) Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if limit ≥ next then
      result := next
    return result
```

The [existing scalar consumer](../Examples/Language/Scalar.lean) uses this
declaration and retains its mathematical minimum specification. The declaration
exports signatures, function identifiers and bodies, the shared program, and
native curried scalar functions. `Implementation.boundedIncrement n limit` has
type `Nat`; its minimum theorem uses the native definition, the increment
equation and ordinary Nat facts. The generated `_action` retains the independent
source observation, `_action_eq_pure` proves equality to `pure` of that native
result for every initial heap, and `_total` supplies its total source contract.
No second implementation proof or manual heap conversion is required.
Without `(pure)`, the existing `P.f`/`P.f_eq` interface continues to expose
`ExceptT Fault (StateT Heap Part)` actions for mutable programs. Native execution
and the compiled RAM runner have different runtimes; function equality neither
sets an instruction price nor hides intermediate work.
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

The checked [traversal](../Examples/Language/Traversal.lean) writes its
read/helper/branch/write loop as `for i in [:xs.length]`. Its mathematical proof
uses native `Array.mapIdx`, `Array.set` and `Array.map` facts. Separate
`guard_contract` and `body_contract` theorems supply the same actual iteration
facts to `variant_contract`; no nested round triple or private execution adapter
is needed. A generated `spec` applies the chosen loop contract directly in native
`mvcgen`. The library restores fixed lexical captures and propagates control;
the author supplies the prefix invariant, descent and actual heap-frame facts.

The [compiled traversal](../Examples/Language/TraversalCompiled.lean) reuses
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
loop's registered coordinate and encoding equations. Generated-view selection
and source-totality conversion remain explicit; shared ordinary-argument resource
rules should hide those routine choices. The mathematical invariant, actual
word ranges and potential inequalities remain author obligations.

The source and RAM results retain `xs.PreservesOutside initial final`: initially
valid disjoint views keep their contents, including slices of one shared object.
No global no-aliasing rule or unchanged-heap assumption replaces these facts.
The shared `BlockSpec.mono` consequence rule reuses native WP monotonicity while
keeping the initial condition available to mathematical postcondition reasoning.

The [recursive factorial](../Examples/Language/Factorial.lean) makes a real
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
The [compiled factorial](../Examples/Language/FactorialCompiled.lean) reuses that
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

## 4. Source semantics and ordinary Lean proofs

Define finite safe execution independently, with a schematic function-level form:

```text
Exec program function arguments heap result heap'

Total program function P Q :=
  forall arguments heap, P arguments heap ->
    exists result heap',
      Exec program function arguments heap result heap'
      and Q arguments heap result heap'
```

Source array bounds and valid views belong to safe source execution. Invalid
operations have a fault outcome, distinct from a returned value; a diverging
computation has no finite successful execution. Total correctness establishes
normal termination, not just absence of a counterexample. Neither source
execution nor source total correctness takes a proposed time budget.

The independent source observations make this distinction explicit.
[`Stmt.eval`](../Complexity/Language/Eval/Basic.lean) has result
`Part (State Γ × Control result)`, preserving the final locals, shared heap and
finite control outcome. `Program.eval program fn args` is an action of type
`ExceptT Fault (StateT Heap Part) (Value result)`. Applying its initial heap gives
`Part (Except Fault (Value result) × Heap)`: fallthrough becomes `.missingReturn`,
including for Unit, while an actual return becomes `.ok value`. Both outcomes
retain the actual final heap; failure does not roll back earlier effects.
`Part.none` means there is no finite outcome; a finite fault is a defined error,
not divergence. Successful result equations are equivalent to finite returned
source execution and therefore include termination.

These noncomputable observations are determined by independent source execution
and determinism. They neither run the lowered RAM code nor choose a value from
the user's mathematical postcondition. The
[composition equations](../Complexity/Language/Eval/Composition.lean) cover
skip, return, primitive binding, sequencing, conditionals and calls, preserving
return/fault propagation and lexical scope. They provide an equational
mathematical interface to the same source program, not a second algorithm.

The [continuation interface](../Complexity/Language/Eval/Continuation.lean)
composes these observations through `Stmt.evalWith`. A normal outcome runs the
supplied continuation; a return or fault bypasses it. The call equation uses
the actual `Program.eval` action in the existing `ExceptT Fault (StateT Heap Part)` monad.
At a function boundary, falling through produces `.missingReturn`. The frontend
uses these proved rules to generate `P.f_eq`, rather than assuming a host `do`
block agrees with the typed source.

In the scalar example, `increment_eval` first rewrites `Implementation.increment_eq`.
Then `boundedIncrement_eval` rewrites its own one-step equation, reuses the helper
result and proves the two minimum cases using ordinary Nat facts.
`FunctionTotal.iff_eval` transports these successful result equations back to
the budget-free source contracts. `Env.forall_cons` and `Env.forall_nil` open
the typed arguments for that generic bridge. The mathematical argument is not
repeated in the contract or compiled-execution proof.

The function contract's precondition takes arguments and the initial heap;
its postcondition takes those same inputs, the returned value and final heap.
An observation equation fixes both the returned value and final heap. This
supports ordinary mathematical contents as ghost specifications when buffer
operations are added, without turning those ghosts into runtime snapshots.

Prove determinism of source outcomes and final state. Mathematical result and
cost observations must not depend on which proof of execution or termination
was supplied. Allocation uses the current object count as its deterministic
fresh identity, rather than an unspecified choice of fresh names.

Source predicates use ordinary Lean values, lists, arrays and relations.
A result specification need not be an independently implemented reference
function. For pure computations, determinism and termination yield ordinary
value equations; for mutation, they yield result/state relations and frames.

### Reuse Lean's termination arguments

For `source_program (pure)`, supply ordinary `termination_by` and, where needed,
`decreasing_by` once. Lean checks the generated native definition; generated
correspondence reuses its recursion principle to establish terminating source
execution with the same result. The mathematical result theorem is then an
ordinary Lean proof, as in the factorial example. This mechanism covers the
supported pure fragment, not arbitrary effectful native recursion.

Effectful total correctness reuses the same mathematical foundation through
source rules, without fuel or a time budget:

- `TotalWP.while_wellFounded` accepts an ordinary `WellFounded` relation.
  `Stmt.observe_while_fixed_spec` exposes it through native `Std.Do` triples
  while fixing immutable captures internally. A named loop's `wellFounded_spec`
  takes a relation on `Loop.Mutable × Heap`; its invariant and normal/return
  postconditions still use named mutable arguments. Descent compares the end
  of a normally completed body with the state before the guard. A false guard
  or early return needs no descent. The existing `variant_spec` is the
  natural-valued `measure` specialization, not a separate termination checker.
- `FunctionTotal.verify_wellFounded` supplies complete source-function contracts
  at smaller mathematical indices using `WellFounded.induction`. The index may
  select different functions and signatures for mutual recursion. This is a
  core proof rule; a convenient named effectful-recursion frontend remains open.

A terminating Lean definition returning `Part α` can return `Part.none`.
Termination of constructing that value does not prove its `Part.Dom`, still
less successful source return rather than a finite fault. `FunctionTotal` or
a strict native triple establishes the required successful execution. Separate
backend proofs retain word-range, stack and cost obligations; those are not a
second source termination argument.

### Public functions, effects and successful termination

The current action type is a general semantic representation, not the desired
mandatory type of every public function. Recursion does not imply a partial
interface, internal mutation does not require exposing the whole heap, and
backend memory faults need not become ordinary algorithm results. Keep general
execution available internally while distinguishing the public cases:

- A pure function, successfully terminating on its declared domain, should have
  ordinary Lean values and equations. Its result must be independent of hidden
  initial state, not merely leave that state unchanged.
- A borrowed mutable operation should have a mathematical contents/result
  contract that preserves actual sharing and frames. Read-only operations may
  still depend on the supplied contents; `NoHeapWrites` alone is not purity.
- A function using private mutable storage may have a functional interface only
  through a proved isolation and result-lifetime boundary. Freezing, ownership
  transfer and copying have different requirements and costs.
- An intended domain error may be an explicit tagged result. Invalid source
  memory access and backend capacity failure are different issues. The present
  compiler proves successful execution under its premises; it does not thereby
  implement every source fault as a checked runtime exception.

The shared user-facing foundation is a mathematical contract over the actual
implementation: typed inputs/results, contents relations, permitted effects,
frames and successful termination. Pure and mutable calls must compose through
these same rules. Mutable programs may use mathematical specifications and
invariants directly, without first constructing another pure algorithm.

The checked pure frontend generates a native total Lean definition and its
typed-core implementation from one supported buffer-free body. It reuses Lean's
recursion infrastructure and the author's one decreasing argument; generated
correspondence proves finite source execution with the native result, not just
equality conditional on successful execution. Scalar, Remainder and Factorial
exercise this path on 0v0, as does OptionalBuffer's nested structured metadata
helper. Self-recursion and acyclic calls are supported;
pure `while`, mutually recursive families and buffers remain unsupported.
Extending this fragment must retain the shared correspondence, not require
a second author-written implementation induction. A domain-restricted
total view needs explicit domain arguments or an implemented error result;
neither backend range premises nor an invented default value replaces this.

The next finite-loop extension must preserve its range origin during elaboration.
The current effectful `for` immediately becomes a while block; removing the pure
frontend's rejection alone would leave a noncomputable observer in the supposed
native function. Retain the captured endpoints, private cursor and the same
normalized body, emit a genuine native finite `for`, and prove its correspondence
to the existing source while once in the library. The shared induction follows
the number of remaining indices and propagates both outer-local updates and
early function returns. The author should neither write a recursive replacement
nor repeat a termination argument for an inherently finite range. Native body
calls must use their existing checked correspondences, including supplied
recursive hypotheses. This extension is planned, not implemented by the present
effectful loop contracts.

This does not accept arbitrary Lean definitions as runtime primitives. The
frontend still controls the executable subset, supported operations and actual
lowering. Specifications remain free to use mathlib. Native Lean evaluation
has its host runtime; the certified complexity remains that of the
corresponding RAM artifact, not Lean's wall-clock execution.

A successful-termination certificate plus a result projection from the same
partial action can be useful shared proof infrastructure. It is not an adequate
replacement for the total frontend: a `Part.get` view is generally
noncomputable, and requiring the full desired correctness theorem before
publishing that view moves rather than removes the proof burden. Termination
may use algorithmic invariants, but no proposed time budget or reference answer
is allowed to define the implementation's result.

The generated native function and program identity have different roles.
Correctness may use ordinary function equality; cost and compilation theorems
remain indexed by the declared program/artifact. A cost function on extensional
Lean functions alone cannot distinguish two implementations with equal results.

The checked pure consumers are Factorial, Scalar and Remainder. Keep evaluating
the complete author proof, including termination and compilation transport,
when extending this fragment. In parallel, Traversal must lose its manual
`Control`/local-tuple/guard-body transport through shared loop contracts. The
pure path cannot be used to declare the mutable proof interface finished.
Conversely, a concise contents contract does not finish the executable pure
interface. For a supported private-state fragment, an ordinary total mathematical
state interpretation can be generated from the same body and related to its
mutable realization. Representation independence, permitted aliasing and result
lifetime remain necessary. A mutable return promises contents at return time;
a pure persistent result needs an immutable representation or proved,
appropriately charged copying/update discipline. Such a bridge is not
implemented, and does not automatically optimize arbitrary persistent updates
into destructive ones.

### Verification-condition generation

Generate source-level conditions from the typed program and prove, schematically:

```text
source_vc_sound :
  SourceVC program function P Q -> Total program function P Q
```

Conditions for bind/call/branch/loop are derived from the independent source
semantics. A call presents its real result and changed heap to the continuation.
Loop conditions expose the named live values and the user's mathematical
invariant/variant. Code navigation, variable bookkeeping and return propagation
are generated. The remaining goals are mathematical implications, callee
contracts and real operation preconditions.

Standard Lean tactics solve these goals. Failed automation leaves the source
condition and location visible. Missing compiler coverage is a language/backend
implementation task, not a request that the algorithm author prove `setReg`
equalities by hand.

### Reuse Std.Do without hiding a second implementation

The [generic Part adapter](../Complexity/Control/Part.lean) reuses mathlib's
`Monad Part` and `LawfulMonad Part`. Its strict `Std.Do.WPMonad` interpretation
is enabled explicitly by `open scoped Part.TotalCorrectness`, not installed as
a global choice. It requires an actual returned value satisfying the
postcondition; `Part.none` has false weakest precondition. The existing monad's
`pure` and `bind` satisfy the required predicate-transformer laws.

The [source adequacy interface](../Complexity/Language/Eval/Verification.lean)
connects source total correctness to the semantic result and native
`Std.Do.Triple`. Functions reuse `ExceptT Fault (StateT Heap Part)` with a false exceptional
postcondition: divergence fails the strict Part obligation, and finite faults
fail that exceptional postcondition. A generic strict Part WP alone need not
reject an error value; the source function specification supplies that policy.
The triple fixes the initial heap as a ghost and tests its equality in the
precondition, so a relational postcondition cannot confuse initial and final
contents. Existing transformer instances supply this composition.

The buffer actions now have native `@[spec]` rules. Reads and slices preserve
the actual heap; writes provide both their real write equation and updated
native contents, so alias/frame facts are not lost at the operation boundary.
`FunctionTotal.triple_spec` converts a supplied source contract into a native
continuation rule, including its actual final heap. Generated `P.f_spec contract`
specializes it to the named function's ordinary arguments. For example, the
buffer consumer uses `have clampSpec := Implementation.clamp_spec clamp_total`
and `mvcgen [clampSpec]`, without unfolding the helper. The supplied contract
retains its initial heap, actual returned value and final heap; no unchanged-heap
condition is imposed by the rule. The
[two-buffer composition](../Examples/Language/TraversalComposition.lean) applies
the existing mutating traversal twice using these named contracts. The first
callee's frame preserves the second input, and the second frame preserves the
first result; neither traversal body is unfolded. The rule does not guess
the callee's mathematical contract or register it globally. The scalar consumer proves
ordinary function equations by rewriting and Nat reasoning, and generated
contract conversion hides the typed argument packing. General mutable helper/loop
composition and elimination of routine ghost-witness packaging remain work
for the author-facing proof interface.
The backend's scalar tactics now compose realization and uniform cost rules;
they do not automatically discover mathematical contracts or recursive bounds.
These are semantic views of the core,
not acceptance of arbitrary host monadic terms as executable primitives.
The laws belong to the interpretation,
not unproved syntactic monad equalities for raw source trees.

A native list iterator visits fixed list values. For a mutable buffer, iterate
a captured index range and perform an actual read in each body; do not import
a snapshot traversal rule as the semantics of general mutable iteration.

An executable wrapper returns the result of the actual interpreter or compiled
runner. It does not choose an answer from a mathematical specification. A
proof-level `Part` observation is allowed, but is not the executable backend.

## 5. Data abstraction and arithmetic realization

### Default container layouts

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
List-valued results use the relational facade below; the complete operation
library remains open.

The first complete callable node-root operation is `List.IsEmpty`: one actual
source body matches the optional root and returns a Boolean without reading a
node. Its ordinary `List.isEmpty` refinement preserves the entire heap. The
checked compiler bridge returns the same halted RAM execution and derives its
full invocation bound from the existing branch, return and call rules. Its
arguments and heap must have the supplied representation and fit the launch
capacity; preloading the inputs is outside that invocation boundary. This
operation does not yet register a native `xs.isEmpty` frontend.

`List.Uncons` also has a checked complete invocation: matching the actual root,
reading a present node and returning an optional head/shared-tail pair. Its
mathematical output is `xs.head?.map (fun head => (head, xs.tail))`, related to
the returned handles at the unchanged heap. The full constant bound includes
the branch, option packaging and outer-call overhead in addition to the node
read. It comes from the same source implementation and measured compiler rules,
not from assigning a price to the ordinary Lean List function. This callable
core operation does not yet register native List method syntax.

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

The opt-in `source_program (native)` frontend accepts ordinary mathematical List
parameters and results. Statically selected pure or imported native callbacks
use actual calls in `List.Fold.program`; `List.cons` and `head :: tail` select the
real allocating `List.Cons.program`. The same block generates an ordinary Lean function and
`_refines`; List handles are related to contents in the actual heap, not encoded
through an `Equiv`. A typed empty list needs no heap object.

The linked-list consumer covers constant accumulators, reordered parameters,
immutable locals, consecutive folds and earlier same-family calls. Its
`NativeConstruction` family additionally constructs and returns lists, composes
two list-returning calls and folds both an old list and its newly allocated
extension. The generated `_action_rel_native` records a successful source result,
its representation in the actual final heap and preservation of old immutable
nodes. Each call transports retained list observations to its actual intermediate
heap through `Representation.list_mono`; no author-written heap adapter or second
algorithm is required. Read-only scalar results retain `_action_eq_native` with
the exact unchanged heap. Allocating functions do not receive that equation.
Native folds accept scalar/product or List accumulators. Their callback may be
an imported pure function or an allocating function from a completed native
family. The latter uses its heap-indexed correspondence, not an unchanged-heap
equation. `NativeLists.reverseAppend` folds an actual cons callback into a List
accumulator; the author's ordinary reverse/append proof reuses Lean's existing
fold/cons identity. Imported native calls, a preceding allocation and subsequent
use of the returned list are checked in the same consumer.

Explicitly typed List conditional bindings now compose those calls:
`let chosen : List Nat ← if flag then do ... else do ...`, with each branch
ending in a List return. The `:=` form uses the same path. Each branch may
allocate and call imported native functions, and a common continuation can
construct or fold the returned list. `NativeBranches.choosePrepend` and
`chooseSum` have checked ordinary mathematical equations and automatically
generated source correspondence on 0v0. The generated proof summarizes each
branch's actual result and heap before proving the common continuation once.
Source lowering uses the existing conditional, a local result slot and an
ordinary continuation; it adds no interpreter or heap-independent List decoder.
Only the selected branch executes. Initializing, assigning and reading the join
slot remain actual source operations for the separate cost proof.

`choosePrepend_execute` connects that same conditional wrapper to a halted RAM
invocation. It retains both original List observations and proves exact cursor
growth of nine words on the true path and six on the false path. Its exact count
includes actual calls, branch and join operations, the common continuation,
initialization and outer call/return/halt. The common arena proof pass composes
these statements from supplied callee costs; the consumer does not build
register or lexical-environment proofs. Word and code/stack/arena conditions
remain explicit, and input loading is outside the count.

The native container fragment still lacks List pattern matching, general
recursion, general element layouts and escaping callbacks. Matching a List
must use the real root/read operations, not free mathematical decomposition.
The existing effectful fold library retains its wider contract. Further control
and operation registration should preserve the same heap-indexed composition
and immutable shared tails.

The compiled `Native.sumFrom` consumer uses those generated declarations and
the existing call proofs to reach the actual wrapper's halted RAM result.
Its ordinary final-sum range condition bounds all intermediate additions, and
its cost includes the wrapper and outer invocation rather than only the imported
fold body. The same source heap is retained. Shared ordinary-parameter fold
interfaces now supply argument-environment, representation-index and zero-growth
resource transport. The consumer retains its mathematical prefix-admissibility
and range proofs, callback resource facts and wrapper call composition. This is
not automatic resource inference for arbitrary native declarations.

The `prepend_execute` theorem in `Examples/Language/LinkedListAllocation.lean`
covers the actual generated allocating wrapper as well. Its shared
constructor-call bridge transports the already measured cons through the
program embedding and existing call/return rules.
The complete count includes the wrapper and outer invocation, not just the
standalone constructor. The same halted result retains the exact new root and
heap, the old tail's contents and a cursor increase of three words. Launch
conditions supply code/stack, rooted input and finite-word facts; the extra arena
capacity is independent of tail length. `prependPair_execute` composes two real
calls to that same generated `prepend`, giving an exact six-word cursor increase
and complete invocation count while retaining the shared old tail. The public
`ArenaExecutionCost.call_measuredOfEq` rule composes those exact observations;
`FunctionArenaResources.call_measuredOfEq` instead consumes independent source
correctness, resource and cost contracts. Both retain the actual intermediate
heap and cursor and charge the existing compiler's call overhead. Sequential
calls reuse the caller depth. These are reusable checked composition rules,
not automatic resource inference for native blocks.

`Examples/Language/LinkedListFoldAllocation.lean` checks the actual generated
`NativeLists.reverseAppend` wrapper through the same halted runner. The fold
invokes the real allocating `ListReducer.push`, and the shared resource rules
derive a full affine instruction bound and a final cursor at most the initial
cursor plus `3 * values.length`. Both original lists remain observable, even
when they share tails. The sufficient internal call depth is three and does
not grow with list length. The theorem counts the wrapper, all callback calls,
initializations and outer call/return/halt; input loading remains separate.
It gives a sufficient fresh-allocation bound, not exact peak live storage.

The checked `Arena.Tactic` pass now constructs that mechanical call/let/return
proof from the actual source body. `ArenaMeasured` is a thin proposition over
the existing execution, readiness and exact compiler count; its postcondition
can retain exact results or upper bounds. `ram_source_arena_step` handles
primitive bindings and returns, stopping at calls. `ram_source_arena_call exact
using cost` consumes a measured callee. The indexed contract form consumes
independent source totality, resource and cost contracts; both accept
`via embedding` for imports. The actual arguments and continuation come from
the statement, and imported function identity comes from its table map.

The `prependPair` and `reverseAppend` migrations include the leaf `prepend` and
`push` wrappers: no hand-written `Args`/`EnvFits`, import transport or operational
return continuation remains in those consumers. `List.Cons.ready_cost` provides
the original constructor proof in ordinary head/tail arguments, not a new
constructor implementation. `List.Fold.measured` similarly exposes the existing
fold entry in ordinary accumulator/list/root arguments. `reverseAppend` now
consumes that actual measured execution through the exact-call form; it no longer
builds a resource-index tuple, `functionPre`, or separate wrapper contracts.
The callback contracts, admissibility, numerical ranges, remaining capacity and
final comparisons stay explicit. The generic contract-call form remains useful
for other indexed operations; the pass does not decode mathematical lists from
handles or infer arbitrary loop/recursion bounds. Automatic selection of further
ordinary-parameter adapters and the remaining loop-view/local conversions are
still open.

The native container frontend composes these heap-indexed operation contracts
at actual intermediate heaps. The existing pure-structure path instead
reconstructs a value from every raw layout using an `Equiv`, and proves an action
equal to `pure` with an unchanged heap. Neither mechanism applies to allocating
lists or to a list handle whose contents depend on the heap. Preserve that useful
scalar path alongside represented-operation correspondence; do not weaken its
purity claim or choose one arbitrary encoding of a shared list.

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

### Abstract objects, not renamed addresses

The source heap contains typed objects with ordinary mathematical contents.
A buffer view identifies an object, offset and length. Slices of one object may
overlap and observe each other's writes. Neither copying a handle nor forming a
view copies the contents.

Initial implementations operate on supplied objects and scratch storage.
Source-level read/write/view and frame laws use upstream collection facts.
The backend heap relation maps objects to physical regions and views to actual
descriptors, reusing `ArrayRef.Rep`, indexed representation and slice/frame
lemmas. Distinct allocated objects have disjoint realizations; distinct handles
need not denote distinct objects. An import must preserve actual input aliases.

Initial aliases must agree on the scalar type of the underlying object. There
is no unchecked pointer reinterpretation: overlapping views cannot silently
import the same cells as unrelated Nat and Bool objects. Cross-type views need
an explicit verified conversion/representation rule before they are supported.

The independent [heap foundation](../Complexity/Language/Heap.lean) now supplies
typed native-array objects, offset/length views, checked read/write/slice
operations and read-after-write/alias/frame laws. A successful write is proved
to be an actual native `Array.set` at the object and cell levels. This foundation
is carried by the source execution state, including across calls and faults.
`Buffer.Contents` observes a valid view as an ordinary native array and transfers
reads and writes to `getElem` and `Array.set`, including updates through aliases.
Read/write/slice statements now invoke these same operations; calls retain their
actual updated heap. `Buffer.Disjoint` uses different objects or disjoint mathlib
`Set.Ico` intervals within one object. `Buffer.PreservesOutside` preserves the
contents of initially valid disjoint views; successful writes establish it, and
it composes through intermediate heaps and permits interval enlargement. This
is not ownership of handles, whole-heap equality or a ban on overlapping aliases.
The named traversal exports this relation with its array result through the
source function contract and the same actual compiled invocation. General
indexed-traversal and effectful-call frame automation remain unfinished.

A checked [source-frame rule](../Complexity/Language/Effects/Heap.lean) uses `Stmt.NoCellWrites`
for the statement and all callees yields `Exec.heap_prefix` and
`Exec.contents_frame` for the actual final heap, including faults. Contents
transport uses [`Buffer.Contents.mono_prefix`](../Complexity/Language/Heap/Prefix.lean)
and `List.IsPrefix`; fresh initialization is allowed, but explicit
cell writes are conservatively excluded. This is contract bookkeeping, not
automatic inference of mathematical ranges, capacities or loop invariants.

The same source program now includes `boundedMapPair`, two ordinary calls to
the existing traversal. Its contract gives both mapped arrays and preservation
of every initially valid view disjoint from both. The two inputs must be disjoint
for this independent-map specification, but may be slices of one object. This
is not a global no-alias restriction. Its
[compiled invocation](../Examples/Language/TraversalCompositionCompiled.lean)
reuses the callee's correctness, realization and cost bounds at the actual
intermediate heap. The stack bound covers the pair, traversal and increment
helper; the independent linear instruction bound counts both traversals and
their real invocation/sequence overheads.

The [borrowed-buffer representation](../Complexity/Computability/Ram/Compiler/Language/Heap.lean)
fixes an object-to-base placement as proof data, represents each complete object
with the existing `Source.ArrayAt`, and observes views through the existing
two-field `ArrayRef` convention. Placement is not a runtime object table.
Its read and write rules reuse `ArrayAt.slice`, native-array store rules and
indexed frames; they separate actual cells of different objects, not overlapping
views of one object. The same register layout now indexes typed fields, with
generic argument packing and receiver proofs. Passing buffer fields and actual
updated heaps through the whole compiler is now proved. A view encoding
need not recover source handle identity: empty views of different objects can
share an encoded endpoint.
Do not infer handle equality from descriptor equality or assume that a successful
access simulation also implements and charges fault checks.

The [operation bridge](../Complexity/Computability/Ram/Compiler/Language/HeapOperation.lean)
connects a successful source read or write to real RAM load/store expressions,
their exact endpoints and the existing compiler-derived instruction counts.
Operand expressions are evaluated dynamically; placement is only a proof
parameter. The source statement cases use these shared rules, and the whole
simulation and runner connection retain the same actual final heap.

Use relations when abstraction forgets storage details; do not require a
bijection between an entire RAM heap and an observed list. Update related views
through the current heap and operation effects, not through obsolete snapshots.

#### Selected initial allocation protocol

The typed core now supports fresh initialized objects as well as supplied ones.
The monotone allocator primitive, initialized-prefix proof, callable RAM runner
and source-heap representation connection are now implemented in
`Memory/Arena` and `Compiler/Language/Arena`. Source `Heap.alloc`, heap shape and
root preservation, and placement transport are also checked. The primitive body
uses `14 * length + 14` instructions; its preloaded function call including
return and halt uses `14 * length + 69`. Session bootstrap separately uses three
instructions. These are costs of the actual emitted code, not host allocation.
The same allocator is parameterized by its five local registers; the inline
typed-operand connection uses `14 * length + 18` instructions, including its
two real operand assignments. It proves the new heap representation and
returned lexical binding at the same execution endpoint. This reuses one
initialization proof and adds no function-table entry.

`Stmt.alloc` now has independent source semantics, its real evaluator,
budget-free correctness and VCG rules, source linking and syntax-directed
lowering. The checked general measured simulation composes allocating bodies
through loops and recursive calls, retaining the actual final heap, extended
placement and cursor. `ArenaReady` and `ArenaExecutionCost` describe the same
source `Exec`; the latter observes actual lowering costs, not a budget required
by source correctness. `FunctionArenaRealizable` packages separate range,
nesting and cursor-dependent capacity conditions and reuses an independent
`FunctionTotal` contract. The [runner connection](../Complexity/Computability/Ram/Compiler/Language/Arena/ProgramExecution.lean)
reaches the halted invocation with positive word width, rooted represented
arguments and sufficient code/stack capacity. Its body count adds two
private-flag instructions, then the actual outer call/return and halt overhead;
input preparation and the one-time bootstrap remain separate.
The checked [allocation consumer](../Examples/Language/Allocation.lean) calls
an allocating `make`, allocates again, then reads the first array when nonempty
and returns it. `retain_runUntil` retains the actual runner count, final arena
and original `ArrayRef` contents, including the empty case. Its `Named.make`
uses `Buffer.alloc`; `named_make_spec` proves ordinary `Array.replicate` contents
with `mvcgen`, without source capacity or time premises. Mathematical ranges
and loop/recursion arguments remain author work; register/placement transport
uses the shared proof. Allocation-aware resource linking transports the same
readiness and costs; the source-frame rule preserves old contents for bodies
without cell writes.
The caller/session owns the live arena; nested calls share allocation progress.
A function return alone does not reset it; an explicit scratch scope has the
lifetime behavior described below.
Caller-supplied scratch remains useful but does not replace fresh results.

The local call bridge now permits different input and output placements and
preserves the caller's rooted descriptors. Legacy heap-mutating imports can
reuse the final heap representation with an explicit metadata frame and final
object-shape containment. These checked boundary rules do not infer metadata
safety from arbitrary `SafeExec`. The separate checked `Arena.Linking` rules
transport readiness and exact costs through typed source embeddings.

At the source level, allocation appends a typed array of the requested length
and initial scalar value, returning the view `(old object count, 0, length)`.
The new object's identity is fresh even for length zero. Source allocation is
abstract and independent of RAM capacity; the corresponding target-success
theorem requires sufficient storage. No compiled out-of-memory result is
promised. A future fallible operation needs its own source/result semantics,
failure behavior and ownership/effect contract.

Growth needs two distinct laws. A single allocation preserves the exact
contents of every old object and supplies the fresh view's `Buffer.Valid` and
initialized-contents facts. The `Heap.ShapeExtends initial finish`
relation instead says that the object domain grows and every old object keeps
its scalar type and length; it deliberately allows changed contents. General
allocating execution proofs must preserve this shape relation, not an exact
contents prefix. It is already proved for the current source `Exec` and for the
standalone heap allocation operation. These are not physical-address claims.

The allocation-aware handle invariant is `Rooted`: a buffer's
object identifier is below the current heap's object count. It is weaker than
`Buffer.Valid`; it does not assert the expected scalar type or a valid view
extent, and does not ban aliases. Track it for live lexical values, suspended
caller environments, actual arguments and returned values. Fresh allocation
establishes validity and rootedness; writes and growth preserve the rootedness
of old handles. The existing checked-access conditions still decide type,
extent and index validity.

This boundary matters because public `Buffer` values can name future IDs even
though the frontend has no ID constructor. Such an old descriptor cannot be
transported through arbitrary placement extension: allocating its future ID
could change its encoded address. The allocation-aware interface states
its rooted-input condition explicitly and preserves it through execution.
Existing no-allocation theorems retain their admitted inputs; they do not acquire a hidden `Rooted`,
full-validity or no-alias premise.

Placement remains proof data, with no runtime object table. One allocation
extends it at the fresh ID with the actual old cursor address and leaves every
old ID's placement unchanged. Agreement on old IDs preserves `bufferRef`,
`valueWords` and environment/register matching for rooted values. This
transport needs no additional offset non-wrapping premise: it preserves the
same existing word encoding, including unused wrapped endpoints. Length and
scalar-operation ranges remain the separate `ValueFits`/realization obligations.
The general allocating simulation returns an existential final placement
extending the initial one, an actual final heap representation, and return
fields encoded with that final placement. A continuation uses this same
post-placement and heap, including when restoring its suspended caller roots.
The fixed-placement certification branch and public results remain for the
no-allocation subset; adding allocation to realization while leaving the old
fixed-placement theorem universal would be unsound.

The initial target protocol reserves RAM address zero for the shared bump
cursor. This is an opt-in arena convention, not a restriction on old RAM
programs. `ArenaRep placement next heapLimit heap target` wraps
the existing `HeapRep` and requires:

- `1 <= next <= heapLimit < 2^w`, with `target.mem 0` the exact word encoding
  of `next`;
- every actual represented object cell has a positive address strictly below
  `next`, leaving `[next, heapLimit)` available for fresh cells;
- the existing object scalar ranges and actual-cell separation. Empty objects
  require no distinct cell or stricter unused-address condition.

This is a prefix reservation, not a compactness requirement: holes and retained
input storage may occur below `next`. `heapLimit` remains the fixed heap/stack
boundary, while `next` is changing allocation progress. Source handles are
still object IDs; the returned RAM buffer is still a base/length descriptor.

The arena/session bootstrap initializes the metadata cell once with an actual,
charged store; it does not run again at each function entry. Preloaded input
contents remain subject to the declared loading boundary, not an implicit free
copy or relocation. An allocation lowers to ordinary existing RAM/IR operations:

1. Read the current metadata cell, obtain `base = next`, and compute
   `end = next + length` under the capacity condition `end <= heapLimit`.
2. Store `end` in the metadata cell to reserve `[base, end)`, then initialize
   each cell with the encoded scalar using actual counted stores and a loop.
3. Only after initialization, expose the base/length fields to the continuation
   and establish the complete appended-object representation.

Initialization invokes no user code and publishes no half-initialized source
object. Its intermediate prefixes use a pending-region/initialized-prefix
invariant, not the complete new-object `HeapRep` before all cells are initialized.
The metadata observation records reserved space even during this initialization.
Length zero reserves no data words but still has the actual metadata/descriptor
overheads of the selected code. The measured theorem derives initialization,
loop, cursor and descriptor costs from that emitted code, not charging a host
`Array.replicate` as a constant-time operation. Fresh temporaries also contribute
to the generated function's local-register and stack-frame bounds.

The current ABI restores caller registers but retains the callee's actual
shared memory; a cursor in that memory therefore survives calls without adding
hidden parameters/results or a new machine-state field. Each subsequent
allocation rereads it, rather than using a cursor cached before an intervening
call. Top-level repeated calls likewise use the actual returned shared state
and final placement. They never reconstruct entry memory or rerun bootstrap.

Metadata protection is an additional invariant, not a consequence of
`SafeExec`: ordinary safe RAM stores may still target address zero. Compiled
source object operations prove that their actual accesses avoid the
metadata. A raw legacy import needs a proved metadata frame, or an
allocator-aware postcondition returning the updated arena representation;
`HeapRep` and an address-capacity bound alone do not suffice. All cooperating
allocating imports use the same session protocol.

Without explicit reclamation, capacity covers retained inputs, metadata and
cumulative fresh allocation across nested and subsequent calls. A separate
stack bound must fit below `2^w`. Returned contents remain mutable through
aliases: a return-time contents contract does not promise an immutable value
forever. Resizing, arbitrary `free`, GC and reference counting are not implemented.

#### Scoped scratch storage

`with_scratch do ...` lowers to the typed core's `Stmt.scope`. It is a lexical
control block, not a function or a value-producing return boundary. Ordinary
fallthrough continues after it; a `return` still exits the enclosing function,
after scope cleanup. Allocate a result outside the scratch scope when it must
survive that scope, and use temporary buffers inside it. This does not implicitly
copy, move or freeze a returned buffer.

`ScopeSafe initial finish control` requires every surviving local handle and
returned handle to refer to an object already present at entry. It is a
root/lifetime condition, not a disjointness, contents or full-view-validity
condition. Mutable buffers contain only scalar Nat/Bool cells. Immutable nodes
have explicit typed tails, and represented heaps require those links to point
to earlier objects: keeping a root's prefix therefore keeps its whole chain.
Node references are source-language values, including inside products and
options. Their rootedness checks the entry object domain; it does not by itself
certify a typed lookup or a valid complete list. Integrating node construction
and reads must retain the backward-link invariant and this reachability
argument. Arbitrary mutable pointers and closures are not covered by the
current scope interface.

On a safe finite exit, the source retains
`finish.heap.take initial.objects.size`: the prefix of the **current** heap.
Writes to old objects and outer locals remain visible. Only objects allocated
inside the scope, including through its callees, are removed, so later allocation
may reuse their identities. This rule also applies to a safe fault exit and
preserves that fault. If the entry-root condition fails, the source retains the
full current heap; normal completion or
return becomes `Fault.regionEscape`, while an existing fault is preserved.
The semantics does not silently leave dangling handles or roll back earlier writes.

`TotalWP.scope` and `scope_compose` prove successful exits from a body contract
that supplies non-escape and the postcondition on this restricted final heap.
The native `Stmt.scope_action_spec` composes the same endpoint conversion with
the body action. Named scratch blocks expose their actual body, equation,
continuation and safe-exit `spec`; no second evaluator determines cleanup.

The RAM lowering saves the actual cursor from address zero in one fresh local,
runs the body, then stores that saved cursor back. Capture and release each
execute three instructions; the latter runs even when the body sets the return
flag. Release does not clear cells or restore old data. The representation proof
keeps precisely the retained source objects and makes the suffix available to
subsequent allocation. `ArenaReady.scope` certifies only safe exits. There is no
compiled escape scanner or claimed runtime implementation of `regionEscape`;
successful target execution remains conditional on non-escape and capacity.

Space must cover every intermediate execution, not just the restored final
cursor. Nested scratch regions contribute their simultaneously reserved space;
sequential reuse need not add their allocation totals. The allocation-aware
memory interface bounds actual accessed addresses by the heap/stack envelope.
That is a sufficient physical workspace bound, not an exact peak-reachable-space
metric. Register, code and I/O storage are separate. The
[source consumer](../Examples/Language/Scope.lean) allocates one result outside
two nested scratch regions, writes it and returns early through cleanup. Its
[compiled theorem](../Examples/Language/ScopeCompiled.lean) repeats that worker
arbitrarily many times within word ranges, returns the same mathematical result,
and bounds every actual access by `entryCursor + 1 + 2*n + 2*frameSize`, independent
of repetition count. The existing source loop proof supplies termination;
resource readiness does not require a second descent argument.

### Nat is mathematical, Word is modular

Source `Nat` arithmetic keeps Lean's mathematical meaning. The initial RAM
realization is bounded-word arithmetic, not bignums. The compiler generates
source-level obligations for every executed intermediate that must be encoded.
For example, `(n + n) / 2` needs representability of `n + n`, not just of
the input and output.

Use the following primitive semantics and implementation policy. A row outside
the current milestone is rejected by that compiler subset until implemented,
not accepted as an uncharged host operation.

| Operation | Source meaning | Initial word-backend policy |
| --- | --- | --- |
| Nat literals, addition and comparison | Lean Nat and Bool operations | Scalar encoding and addition-range obligations; current scalar backend |
| Nat multiplication | Exact natural multiplication | Proved lowering with an actual intermediate-product range condition |
| Nat subtraction | Saturation at zero | Proved comparison mask applied to the wrapping word difference; no subtrahend-order premise |
| Nat division and modulo | Lean semantics, including `n / 0 = 0` and `n % 0 = n` | Existing word operations already match these zero cases; proved lowering requires representable operands, not a nonzero divisor |
| Explicit BitVec operations | Their specified modular/word semantics | Matching word operations and proved representation |

The first lowering is syntax-directed, not selected by a user's proof.
An invariant may discharge its range conditions; proof-guided removal of a
branch is a later verified optimization with its own cost connection. An
unresolved range condition does not authorize changing source semantics or
silently narrowing a published theorem's input domain.

Existing modular Word examples retain that meaning when migrated. No claim is
made that every unbounded-Nat program runs at arbitrary word width or that
arbitrary-precision arithmetic costs one RAM transition.

The current nested-expression consumer implements `n - (n / d) * d`. Its source
result follows from the ordinary Nat remainder identity, and the shared compiler
transfers that result to the actual callable implementation. Its range and cost
proofs remain separate; the bound counts division, multiplication and saturating
subtraction, not a different implementation using one remainder instruction.

### Three kinds of obligation

- Source correctness: array validity, mathematical invariant and termination,
  independent of the selected backend width, stack layout and proposed time
  bound. Explicit source `BitVec w` types still have their stated width semantics.
- Backend realizability: intermediate scalar ranges, physical storage for the
  represented objects, and sufficient maximum call nesting/storage.
- Backend mechanics: fresh slots, argument encoding, receiver updates, saved
  locals, code placement and instruction correspondence, solved by compiler
  proofs.

The second group is derived from source-level facts and exposed in those terms
when it cannot be solved automatically. A well-founded termination argument
does not automatically give a tight call-stack bound. Shared rules can derive
such bounds for supported recursion patterns without confusing them with time.

The current scalar realization API has shared `RealizationWP` rules, but its
consumer no longer applies them one source constructor at a time.
`ram_source_realize` opens ordinary arguments, reuses the supplied callee's
realizability and correctness facts and simplifies environment bookkeeping.
Without `using`, it stops at a call. `ram_source_call using resource, specification`
then consumes just that call's supplied realizability and source contracts,
retaining its actual returned value and final heap before stopping at the next
call. The caller can use a frame consequence to establish that next call's input.
The underlying intermediate-range and call-nesting facts remain genuine
source-level obligations. General callee selection and recursive automation
remain work for the richer language.

## 6. Automatic proof transfer to the existing backend

A lowering artifact contains the actual `Stmt/Func` program and its concrete
representation/layout plan. Shared structural theorems relate source execution
to that artifact. Elaborator-generated certificates instantiate those theorems;
they do not search for a new simulation proof for each user program.

The artifact is fixed by the declaration and backend configuration. Its
certificate applies to all represented legal inputs, not a selected runtime
input, execution witness, time budget or correctness proof. A width-parameterized
artifact family is allowed under a fixed compilation/width policy; unrelated
per-input programs are not a uniform implementation. Later verified optimization
plans must respect the same boundary.

Required proof shape, with names only schematic:

```text
lowering_sound :
  Compiles source artifact ->
  Exec source input heap result heap' ->
  InputRep artifact input heap targetEntry ->
  RealizationConditions artifact thisSourceExecution ->
  exists targetFinish,
    TargetSafeExecution artifact targetEntry targetFinish
    and OutputRep artifact result heap' targetFinish
```

A semantic definition of realization conditions can quantify over the source
execution. Its public proof interface must instead generate arithmetic,
region-size and source-recursion conditions with a proved sufficiency theorem.
Do not ask users to assume target termination, an unexplained trace premise,
or precisely the register execution the compiler is supposed to establish.

Prove the source-to-IR cases once: values/operations, lexical scope, sequencing,
both branches, current-heap reads/writes, calls, loop iteration/exit and returns.
Maintain lexical environment and heap relations inside these proofs. The call
case composes the parameter/result relation and callee theorem, preserves source
caller locals and retains shared effects. Recursive soundness may induct over
finite source execution; source termination is proved independently.

Then compose with the existing `FunctionExec`/safe execution to RAM simulation
and runner theorems. Supported source programs require no per-function raw AST
adapter, layout record or proof that their whole body equals a library template.

A total source theorem plus a verified realization derives the compiled
termination theorem. The user does not supply an additional unexplained
`Halts` assumption. Code/stack/width obligations remain genuine and are
translated through the generated plan.

## 7. Separate cost, over the same core execution

Define a cost observation of the same typed core, parameterized internally by
a proved backend interpretation. It is not a second user program or a
source-visible budget. Require:

- erasure: forgetting cost yields exactly the source execution;
- instrumentation: each source execution admits that cost observation;
- determinism: the chosen interpretation fixes the count for that execution,
  independently of proof terms used to establish execution or termination;
- noninterference: source branch selection, effects and termination do not
  inspect the count or the proposed bound.

These are the intended interface obligations. Current `ExecutionCost` is
indexed by successful `RealizedExec`, and every such execution admits a count;
this is not yet instrumentation of every unrestricted source execution.
Conditional `FunctionCostBound` alone can be vacuous when execution is not
realizable. Publication must continue to combine independently established
source totality, realizability and the bound, as the existing runner bridge does.

The RAM interpretation comes from the actual lowering/layout. Its charges
include operand evaluation, copies, descriptor fields, guard/jumps, traversal
setup/load/update, argument preparation, callee frames, return fields, receiver
updates for calls inside the body. A source call does not have a
layout-independent exact constant. Ghost mathematics is erased; actual runtime
work is not.

Use one accounting convention: `sourceCharge` covers the selected lowered
function body and all complete internal calls. This includes the body's private
flag initialization, as well as checks crossed after an early return. Complete
functions omit the empty final dispatch; a generic wrapper with a normal
continuation still charges its actual dispatch. `outerOverhead` covers only the external entry trampoline,
outermost calling convention and final halt. No instruction belongs to both.

The upper-bound connection must have the useful direction:

```text
actualTargetSteps <= sourceCharge artifact sourceExecution + outerOverhead artifact
```

Exact equality is useful for some fragments, not required for every
optimization or upper bound. The source charge and outer overhead are proved
from emitted code; user-selected operation prices or unchecked ticks do not
establish a RAM bound.

The initial publication theorem combines source total correctness, realizability
and a bound on that same source execution. Forward finite-execution simulation
with a cost bound, followed by target determinism, suffices to identify and bound
the actual runner. It does NOT by itself supply an unconditional converse for
every completed target trace. A conditional target-bound API without source
termination additionally requires completed-trace reflection or an equivalent
adequacy theorem; keep that as a distinct obligation.

Cost composition follows actual returned values and updated data in execution
order. Use a shape/length/frame consequence of a behavioral contract when that
is all a bound needs; retain content facts when the work depends on them.
Do not repeat sorted-content reconstruction merely to recover lengths, and do
not remove premises from existing time contracts without proving replacements.

Use mathlib sums, asymptotics and recurrence results, plus the existing potential
lemmas. Generating structural cost obligations does not automatically discover
the right recurrence, potential or invariant. Ordinary behavioral equality
allows mathematical reuse but never transfers an algorithm's cost by itself.

The current [structural scalar rules](../Complexity/Computability/Ram/Compiler/Language/CostBound.lean)
expose `StmtCostBound` for a source statement and its entry values. This is a
conditional upper bound on the existing `ExecutionCost` observation, not a new
interpreter or termination proof. Rules compose primitives, returns, sequencing,
the selected branch and actual calls without making consumers destruct the
execution relation. `FunctionCostBound.of_stmt` adds the returning-body wrapper
once; `callCost` still comes from the actual calling convention. The proved
`callCost_eq_add` separates the body count from that fixed generated overhead,
keeping frame and return layouts out of recursive arithmetic proofs.

The scalar consumer now uses `ram_source_cost` to compose these rules. Its uniform branch bound
does not need the helper's mathematical result; a result-dependent continuation
can instead reuse a consequence of an existing source contract through the call
rule. Structural rule selection and intermediate bounds are generated from
the existing theorems; ordinary arithmetic tactics finish the requested
inequality. When the guard follows from source values and local facts, the
tactic selects only that branch through the proved `ite_true`/`ite_false` rules.
Otherwise it retains a uniform maximum; it does not guess a symbolic decision.
By default the tactic uses a uniform continuation bound; this does not require
an unchanged heap or discard the callee's result properties. Named
`ram_source_call (next := fun value heap => ...) using resource, specification`
also exposes the general result/state-dependent numerical rule. The author
supplies the numerical function, while the shared rule retains the actual
callee result and postcondition. `StmtCostBound.call_of_spec` and `call_seq_uniform` retain
the supplied source postcondition while inferring the continuation's uniform
bound. The latter specializes `call_seq`, which hides standalone call/skip
execution cases and charges the actual normal sequence dispatch.

For effectful composition, `ram_source_cost (xs ys limit)` stops before the
first call. `ram_source_call using resource, specification` applies one selected
cost contract and source contract, then continues structurally until the next
call. The two-buffer composition uses this interface twice, with separate
contracts for the two mathematical contents. It no longer opens argument
environments, restores result scopes or supplies intermediate structural bounds
by hand. Its actual intermediate-heap frame argument and final cost inequality
remain explicit. Contract selection is not automatic; the existing single
`using` mode still reuses its supplied contract throughout the structural pass.

Uniform structural budgets can be inferred rather than restated as numeric
constants. The traversal keeps a natural-number witness together with its
`StmtCostBound` proof; `ram_source_cost_step` fixes that witness by applying the
existing compiler-derived rules. The witness is introduced before arbitrary
locals and heaps, so it cannot silently depend on a particular observed state.
The same method uses `ram_source_cost_intro` to infer the complete function
wrapper around a supplied loop or callee bound. Direct, two-call and imported
clients refer to the resulting named bound rather than copy its expression.

`StmtCostBound.whileLinearBound` supplies the existing loop rule's structural
charges for a uniform guard/body budget. Its exit and step lemmas leave the
author the mathematical remaining-iterations decrease; early return retains
its separate obligation. This does not infer a loop invariant, discover a
nonlinear recurrence, or force a state-dependent bound to be uniform. Those
cases continue to use the general potential and dependent-call rules.

The function-exit optimization separately removes the redundant final dispatch.
The actual body is three instructions shorter, its inferred register bound is
unchanged, and measured lowering charges initialization plus the core (`+2`).
The generic statement wrapper and its returning-path `+5` are unchanged.

## 8. Migration and module boundaries

Keep `Complexity/` as the only reusable library root. The
`Complexity/Language/` subtree holds typed syntax, independent semantics,
source proof rules and frontend support. Its semantics/proof modules must not
import RAM. Backend realization and lowering live under the existing RAM topic
and import both the language and current compiler. Final file splits follow
actual dependencies; do not create a hierarchy of empty placeholder modules.

Reuse rather than replace:

| Existing foundation | Role |
| --- | --- |
| Lean/Std/mathlib values, `Part`, monad transformers, `Std.Do` | Mathematical data and semantic proof infrastructure |
| `Ram.Source.Stmt/Func`, safe and measured execution | Backend IR and proved execution rules |
| Local compiler, typed/raw call and runner bridges | Actual code, safe execution and cost transfer |
| Array/indexed representation, slice and frame lemmas | Physical realization of abstract source objects |
| Recurrences, `IsBigO`, potentials | Mathematical analysis after source obligations are obtained |
| Named parser, source metadata and RAM tactics | Reusable frontend pieces, active backend proof tooling, certificate support and compatibility |

The existing `ram_def` interface remains supported while high-level declarations
are introduced separately. Do not silently change old word semantics, input
domains or measured programs. The independent high-level semantics is new work;
existing StateM postcondition wrappers do not count as its implementation.

### Lemma reuse through the connection layer

Old-DSL contracts, representation/frame lemmas and cost results should reduce
high-level proof work through `Compiler/Language`. This layer imports both sides
and proves reusable transport rules; the independent source semantics does not
import RAM or gain external-function forms merely to reuse a theorem. Ordinary
mathematics already in mathlib should be reused directly.

An algorithm author should apply a source-facing theorem whose proof reuses the
old library. The connection layer handles value representation, routine frame
transport and invocation correspondence once for a supported construction, not
through one hand-written register adapter per algorithm. Genuine range, aliasing
and storage conditions remain visible in source terms.

Transfer must respect its logical direction. The existing forward simulation
can map a realized source execution to the target and recover its result
property using an old contract and target determinism. It cannot derive source
termination from target termination alone. Such an API needs a separate proved
reverse/progress connection. Similarly, behavior equality alone cannot transport
an exact instruction count or justify replacing one implementation by another.

Selecting a verified old implementation for a high-level library call belongs
in this connection layer too. Its actual code, dependencies, behavior and cost
must be linked by proved correspondence. That capability is distinct from the
immediate goal of reusing lemmas; adding a foreign-call node by itself does not
reduce high-level correctness proofs.

A new lowering can produce different code. For migration, record whether it is
definitionally the old program or prove the new behavior and cost bounds.
Behavioral correspondence does not preserve old exact constants automatically.

## 9. Acceptance and unresolved implementation choices

The [roadmap](ROADMAP.md) sequences implementation and the parallel backend proof
track. This language's criterion is algorithm-author experience; the backend
track additionally evaluates how maintainers prove and change lowering cases
using reusable interfaces. Neither is measured by the number of exported tactics.

A genuinely different mutable loop must be proved using source variables,
ordinary contents and a mathematical invariant. Its helper return, branch and
store compose without any algorithm-specific register proof. Search then
exercises a different loop shape; recursive sort exercises recursion and
multiple buffers. Their compiled bounds concern these same declarations.

Fixed semantic boundaries: independent typed core, explicit executable
operations, actual shared-state behavior where used, budget-free correctness,
checked lowering, backend-derived costs and preservation of real safety
conditions. These do not fix every public function to the current heap-action
type. Extensions beyond the checked buffer-free pure frontend and abstraction of
local mutable storage still require the design and correspondence work above.

The scalar implementation now fixes typed lexical contexts, the `source_program`
spelling, one-step monadic equations and a strict scoped Part/Std.Do interpretation.
Shared cost rules and focused tactics remove some structural bookkeeping from
scalar consumers. The roadmap now separates function-definition experience,
mutable proof contracts, structured values, memory management and public resource
claims. Scalar simplification or another imported-call variant cannot finish
those capabilities. No choice may define high-level meaning through
lowering, accept manually entered instruction prices or expose register proofs
to algorithm authors.

Richer data operations and general lifetime/encapsulation interfaces remain
scheduled capabilities, not assumed consequences of the checked scoped allocator
or a mathematical view. Arbitrary Lean compilation,
general closure conversion, a new ownership calculus, bignums, a new machine
model and a full optimizer are not prerequisites for the first usable language.
