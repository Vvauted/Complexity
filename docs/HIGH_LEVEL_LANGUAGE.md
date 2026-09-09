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
Generated contract equivalences hide argument-environment packing;
realization/cost rule application is still explicit.
Full source proof automation, mutable data and loops are not yet supported. The
[roadmap](ROADMAP.md) records these boundaries and defines completion gates.
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

Loops carry their live source values explicitly; surface mutable locals are
translated to these values by a shared elaboration/normalization rule. The
algorithm invariant is expressed in those values, never in an environment-to-
register decoding supplied by the algorithm author.

Specify normal continuation and function return as different control outcomes
from the start. A return crosses nested blocks and loops and is caught by the
function boundary; sequencing executes its tail only on normal continuation.
The scalar compiler already handles returns through nested bindings, branches
and sequences using a private flag, without duplicating the remaining code.
The future loop lowering must propagate the same control outcome.
`break/continue` and tagged
`Option/Sum` values are subsequent supported constructs, with real control and
tag/payload lowering, not dummy returned words.

First-order functions are sufficient for the initial recursive algorithms.
Static specialization may later support generic combinators; dynamic closures,
arbitrary dependent runtime types and a general effect-handler system are not
prerequisites. Function contracts are reusable across callers and imports.

### Current scalar surface and intended data extension

The [scalar frontend](../Complexity/Language/Syntax.lean) accepts ordinary typed
headers and `do` bodies inside `source_program`:

```lean
source_program Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let next ← increment n
    if next ≤ limit then
      return next
    else
      return limit
```

The [existing scalar consumer](../Examples/Language/Scalar.lean) uses this
declaration and retains its previous typed core definitionally. The declaration
exports signatures, function identifiers and bodies, the shared program, and
curried mathematical observations. In particular,
`Implementation.boundedIncrement n limit` has type `Part (Except Fault Nat)`.
The generated `Implementation.boundedIncrement_eq` unfolds one source body into
ordinary `ExceptT Fault Part` `do` notation, retaining the named `increment`
call. It is not a simp rule: recursive callees are not expanded automatically.
The user proves the minimum result from this equation and the helper's proved
result, not from a second implementation. The observation is noncomputable,
not an executable replacement for the compiled runner.
All function signatures are collected before lowering the bodies, so named
calls refer to the same source program rather than arbitrary host callbacks.
The available surface is Nat/Bool/Unit, immutable `let`, calls, `if` and `return`;
it does not yet supply mutable locals, buffers, loops or automatic proofs.

The buffer program below remains a design sketch, not accepted source syntax:

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
`Part (Env Γ × Control result)`, preserving the final lexical environment and
finite control outcome. `Program.eval` has result
`Part (Except Fault (Value result))`: fallthrough becomes `.missingReturn`,
including for Unit, while an actual return becomes `.ok value`.
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
the actual `Program.eval` action in the existing `ExceptT Fault Part` monad.
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
`Std.Do.Triple`. Functions reuse `ExceptT Fault Part` with a false exceptional
postcondition: divergence fails the strict Part obligation, and finite faults
fail that exceptional postcondition. A generic strict Part WP alone need not
reject an error value; the source function specification supplies that policy.

Next connect the compositional equations and shared operation specifications to
`@[spec]`, `mvcgen` and focused source proof automation. The current scalar
consumer already proves ordinary function equations by rewriting and Nat
reasoning; the generic contract conversion still explicitly opens `Env`.
The frontend does not automatically discharge mathematical contracts,
realization conditions or cost bounds. These are semantic views of the core,
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
consumer still opens source bindings, transports returned values and constructs
`EnvFits` proofs explicitly. Removing this environment bookkeeping is pending
automation work; the underlying intermediate-range and call-nesting facts must
remain genuine source-level obligations.

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
flag initialization and final dispatch, as well as checks crossed after an
early return. `outerOverhead` covers only the external entry trampoline,
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
once; `callCost` still comes from the actual calling convention.

The scalar consumer now uses these rules explicitly. Its uniform branch bound
does not need the helper's mathematical result; a result-dependent continuation
can instead reuse a consequence of an existing source contract through the call
rule. Structural rule selection, argument transport and the final inequality
are not yet generated automatically. This reduces proof plumbing without
changing the emitted code, accounting convention or separation from correctness.

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
Shared cost rules remove execution case analysis from the scalar consumer.
M1 remains open: structural realization and cost-rule application still need
source-facing automation and reusable specifications. Improve these alongside
the lemma-transfer bridge and the first complete borrowed-buffer path; do not
require perfect scalar automation before heap effects and loops can inform the
proof interface. No choice may define high-level meaning through
lowering, accept manually entered instruction prices or expose register proofs
to algorithm authors.

Richer data operations and allocation remain scheduled capabilities, not
assumed consequences of a mathematical view. Arbitrary Lean compilation,
general closure conversion, a new ownership calculus, bignums, a new machine
model and a full optimizer are not prerequisites for the first usable language.
