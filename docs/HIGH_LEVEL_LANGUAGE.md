# High-level language design

Status: architecture under implementation. The independent scalar core now has
source correctness rules, generic whole-function lowering and proof transfer to
the existing executable RAM runner. Return-flag lowering avoids continuation
duplication and has exact static code-size formulas. A separate cost observation
of realized scalar executions now transfers source bounds to the actual runner,
including internal calls and the outer invocation overhead. The Lean-like
scalar `source_program` surface, independent `Part` observations, compositional
evaluation equations and a scoped strict Std.Do interpretation are now present.
Generated one-step function equations support ordinary mathematical correctness
proofs; shared structural rules compose separate cost bounds. The generated
curried functions are noncomputable semantic observations, not `#eval` runtimes.
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
normal-continuation proofs and a variant rule over named mutable locals.
The complete buffer traversal proof now gives its ordinary `Array.map` result,
preservation of disjoint views, termination, compiled invocation and independent
linear instruction bound.
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
embeddings. An imported program can itself contain imports. Transport of compiled
resource bounds remains separate work; source action equality does not supply it.
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

### Values and operations

The initial language design includes mathematical `Nat`, `Bool`, `Unit`,
finite products, and borrowed buffers/views of supported scalar types.
Explicit `BitVec w` values retain modular arithmetic when that is intended.
Products need genuine field encodings at calls and returns; the backend's
current word/array/unit facade does not already provide arbitrary products.

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
The generated loop rule takes an invariant and variant over ordinary mutable
locals, fixing immutable captures with proved lexical preservation. Authors
still supply the mathematical invariant and descent proof.
`break/continue` and tagged
`Option/Sum` values are subsequent supported constructs, with real control and
tag/payload lowering, not dummy returned words.

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
again. Source observation equality does not by itself transport compiler-derived
realization or costs; those connection-layer rules remain to be supplied.

### Current surface and intended traversal extension

The [scalar frontend](../Complexity/Language/Syntax.lean) accepts ordinary typed
headers and `do` bodies inside `source_program`:

```lean
source_program Implementation where
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

The [existing scalar consumer](../Examples/Language/Scalar.lean) uses this
declaration and retains its mathematical minimum specification. The declaration
exports signatures, function identifiers and bodies, the shared program, and
curried mathematical observations. In particular,
`Implementation.boundedIncrement n limit` has type
`ExceptT Fault (StateT Heap Part) Nat`.
The generated `Implementation.boundedIncrement_eq` unfolds one source body into
ordinary monadic `do` notation, retaining the named `increment`
call. It is not a simp rule: recursive callees are not expanded automatically.
The user proves the minimum result from this equation and the helper's proved
result, not from a second implementation. The observation is noncomputable,
not an executable replacement for the compiled runner.
The scalar equation `Implementation.increment n = pure (n + 1)` describes the
whole action: it returns that value and preserves every initial heap. No empty
heap or separate pure evaluator is chosen. This equation describes behavior,
not zero execution cost or absence of intermediate work.
All function signatures are collected before lowering the bodies, so named
calls refer to the same source program rather than arbitrary host callbacks.
A named function returning `Unit` can appear directly as a statement; other
results require an explicit binding. The source call still executes, catches
the callee's return at its own boundary and passes its actual heap to the next
statement. No dummy return word or host callback is introduced.
The available surface also accepts `Buffer Nat` and `Buffer Bool`, their length,
`let x ← xs.get i`, `xs.set i x` and `let ys ← xs.slice offset length`.
These operations use the actual current shared heap. `let mut`, `x := expression`
and `x ← action` update existing typed locals; the latter reuses the same real
calls, reads and slices. An immutable nearest binding cannot be bypassed to
assign an outer mutable binding with the same name. The native equation uses
Lean's own mutable `do` and branch joins, not a second environment monad.
Surface `while` now generates observations and equations for the actual parsed
guard and body, together with a named-local `variant_spec`. General proof automation
remains unfinished. The buffer consumer separately
checks its source specification and the compiled invocation of that declaration.

Assignments also cover borrowed descriptors: changing a local handle does not
copy or change the referenced heap object. The compiler proves contiguous
fields and distinct live-variable slots for generated layouts, then reuses a
shared update correspondence. Buffer self-assignment is a safe sequential copy,
not an implicit snapshot or an extra no-alias requirement. Its real moves are
still charged. Ordinary source proofs never supply these layout arguments.

The indexed `for` notation below remains a design sketch. The checked
[while traversal](../Examples/Language/Traversal.lean) already expresses the
read/helper/branch/write body with an explicit mutable index. Its complete
correctness and termination proof reuses native `Array.mapIdx`, `Array.set` and
`Array.map` facts. The generated `boundedMap_loop1.variant_spec` needs an
invariant and descent measure only on `i` and the heap; `xs` and `limit` are fixed
by generated lexical preservation proofs. This preserves the buffer descriptor,
not its contents. The complete source proof now composes native `Std.Do`
operation rules and uses the strict `StateT` adequacy interface to recover actual
result equations. It no longer unfolds WP, `Part.bind`, environments or control
execution trees. Selecting the loop contract and mathematical contents remains
explicit. The [compiled traversal](../Examples/Language/TraversalCompiled.lean)
now reuses this source proof and establishes the same final array contents and
a linear instruction bound for the actual halted invocation. Word ranges,
preloaded heap representation and code/stack capacity remain explicit. Shared
realization rules reuse source termination rather than requiring a second
decreasing measure, and cost composition reuses the source array invariant.
Fixed-capture realization and cost rules now reuse the generated lexical frame,
so their invariants and potentials need only the mutable index and heap. A single
native `round_spec` retains the mathematical guard result and the body contract
at that guard's actual final locals and heap. Source correctness composes its
native triple; the separate resource proofs extract its facts through
`Part.TotalCorrectness.stateT_post_of_eq`. This removes repeated index/heap
substitutions and guard-to-array-bound reasoning from the compiled consumer;
no additional specification wrapper or execution relation is needed. Choosing
the generated views/frames and applying the supplied contract remain explicit.
The source function contract also exports `xs.PreservesOutside initial final`:
every initially valid disjoint view retains its contents, including another slice
of the same object. The strengthened compiled theorem retains this property at
the same represented final heap without changing the program or its cost bound.
Further named-loop automation remains separate work.

The shared [native consequence rule](../Complexity/Control/Triple.lean),
`Std.Do.Triple.mono`, directly reuses WP monotonicity. Combined with Std's
`Triple.and`, it lets `loop_spec` and `loop_frame_spec` compose result and frame
facts about the same guard/body action without unpacking `Part` execution
witnesses. Their public statements, `round_spec`, source program and costs are
unchanged; invariants, descent and genuine frame consequences remain explicit.

The [recursive factorial](../Examples/Language/Factorial.lean) makes a real
source self-call on `n - 1`. Rewriting its generated one-step equation and using
ordinary `Nat` induction proves the same action equals `pure (Nat.factorial n)`:
finite success with the expected result and preservation of every initial heap.
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

The implemented scalar observations make this distinction explicit.
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
was supplied. When allocation is introduced, use a deterministic fresh-object
supply in the abstract heap rather than an unspecified choice of fresh names.

Use ordinary well-founded reasoning for loops and recursion. The implementation
must provide reusable rules for arbitrary bodies, not an algorithm-specific
interpreter or a new induction framework for each example.

Source predicates use ordinary Lean values, lists, arrays and relations.
A result specification need not be an independently implemented reference
function. For pure computations, determinism and termination yield ordinary
value equations; for mutation, they yield result/state relations and frames.

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

Allocation is an explicit later milestone: source freshness, a concrete allocator,
initialization, actual capacity and charged stores. Start with a simple arena,
not a garbage collector. Returning a freshly allocated container requires that
its region remain live. Reclamation needs its own lifetime rules. A host-created
`Array` is not a free RAM allocation.

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
| Nat literals, addition and comparison | Lean Nat and Bool operations | Scalar encoding and addition-range obligations; M1 subset |
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
The tactic's call-continuation bounds remain uniform numerical bounds;
uniformity does not require an unchanged heap or discard the callee's result
properties. Truly result/state-dependent numerical bounds use the general
explicit call rules. `StmtCostBound.call_of_spec` and `call_seq_uniform` retain
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

Fixed decisions: independent typed core, explicit executable operations,
shared mutable heap, budget-free behavior, checked lowering, backend-derived
costs and preservation of real safety conditions.

The scalar implementation now fixes typed lexical contexts, the `source_program`
spelling, one-step monadic equations and a strict scoped Part/Std.Do interpretation.
Shared cost rules and focused tactics remove structural bookkeeping from the
scalar consumers. M1 remains open: richer source specifications, general callee
selection and recursive/data-dependent automation are unfinished. Improve these alongside
the lemma-transfer bridge and the first complete borrowed-buffer path; do not
require perfect scalar automation before heap effects and loops can inform the
proof interface. No choice may define high-level meaning through
lowering, accept manually entered instruction prices or expose register proofs
to algorithm authors.

Richer data operations and allocation remain scheduled capabilities, not
assumed consequences of a mathematical view. Arbitrary Lean compilation,
general closure conversion, a new ownership calculus, bignums, a new machine
model and a full optimizer are not prerequisites for the first usable language.
