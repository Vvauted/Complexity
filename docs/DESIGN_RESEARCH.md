# High-Level Verified Programming and Cost Semantics

## Conclusion

Complexity should expose one high-level implementation with complementary
equational and contract-based proof interfaces. Pure, terminating functions
should support ordinary Lean equations. Mutable algorithms should support
mathematical contents specifications, local reasoning and loop invariants.
Neither interface should require algorithm authors to reconstruct the
interpreter, register layout or compilation proof. Both must identify the same
declared implementation and its actual compiled artifact.

The strongest architectural precedent is a combination, not one system copied
wholesale: proof-producing translation from HOL4/CakeML and Rocq; abstract data
refinement and verification-condition generation from Isabelle and CFML;
effect and ownership elaboration from F*/Pulse; and the distinction between
behavior and implementation cost from CALF/Decalf. These approaches solve
different parts of the problem. Their cost models, termination guarantees and
trusted boundaries are not interchangeable.

The recommendation is therefore **contract-centered, proof-producing
compilation with a genuine pure-function path**, rather than either a universal
heap monad at the public boundary or a universal requirement to generate a pure
function before verifying any program. A pure facade over internal mutation is
an additional, justified abstraction: it needs a contents relation, isolation
and an explicit result-lifetime policy. It must not silently copy an algorithm
into a second user-maintained implementation.

This report concerns sequential algorithm verification in Lean with mathlib
and the existing word-RAM backend. Evidence is version-qualified through
September 2026. The repository baseline is `a1e99a9`; proposals below are not
claims that the corresponding interfaces are already implemented. Named source
files and theorem statements provide implementation evidence; no claim is made
that external libraries were rebuilt or that every development branch was
audited.

## 1. Requirements and present boundary

The intended experience has four distinct obligations. A declaration must
describe an actual program; its specification must use ordinary mathematical
objects; its correctness proof must establish successful termination on the
declared domain; and its resource proof must describe that implementation on a
specified computational model. A short theorem statement does not establish a
short proof workflow, and an executable host function does not establish a
cost-preserving target implementation.

At the baseline, the independent typed source supports scalars, shared borrowed
buffers, mutable locals, branches, effectful-guard loops, recursion and imports.
Its generated function is a semantic action in
`ExceptT Fault (StateT Heap Part)`, not an ordinary executable total Lean
function. The actual factorial proof still exposes this action; traversal
proofs still expose loop/control bookkeeping. The source heap has existing
Nat/Bool arrays and overlapping views, but no allocation or reclamation
statement. Source execution and measured RAM execution are already connected;
this is a foundation to retain, not replace with an unconnected cost monad.[^1]

The success criterion is the complete author workflow. For factorial, the
author should supply the relevant mathematical induction without another
hand-written induction establishing the generated implementation. For an
array loop, the author should supply contents invariants, descent and genuine
range conditions, without transporting local-variable tuples or heap-monad
equations. A caller should consume the callee's proved mathematical contract
and resource bound without reopening its body.

Ordinary specifications need not be reference algorithms. Sortedness and
permutation, membership, shortest-path optimality, and equality to
`Nat.factorial` are mathematical properties. Reusing such definitions from
mathlib is different from requiring a second independently maintained program
with the same control flow.

## 2. Comparative evidence

The following boundaries refer to the specific sources discussed below, not
to every tool or research branch associated with each prover.

| Approach | Author-facing proof interface | Resource endpoint in the cited evidence | Important limitation |
| --- | --- | --- | --- |
| Isabelle native `time_fun` | HOL functions, equations and generated time functions | Selected source-operation model | The cited manual explicitly lacks a verified underlying model. |
| Isabelle timed refinement/Sepref | Mathematical specifications, invariants, representation assertions | Heap-operation costs in 2019; LLVM-operation costs in 2022 | A verified machine-code cost chain is not supplied by the latter paper. |
| Rocq/CFML and time-credit work | Lifted mathematical contracts, `xapp`, frames and abstract cost functions | Costed source-language evaluation in the historical time-credit work | Current CFML2 source and older timing artifacts must not be conflated. |
| HOL4/CakeML | Native function translation, monadic translation, characteristic formulas | Verified machine behavior; separate machine-connected space safety | Functional compilation does not automatically provide machine-time bounds. |
| Rocq certifying extraction | Ordinary supported Gallina functions and generated certificates | Counted call-by-value lambda-calculus reduction | This cost model is not word-RAM. |
| F*/Pulse | Mathematical postconditions, mutable syntax and ownership elaboration | Source correctness/safety and practical native extraction | General Pulse contracts are partial; native compilation has a trust boundary. |
| Agda CALF/Decalf | Cost-aware equations and a behavioral phase | User-selected cost effects in a logical framework | The Agda embedding is not an axiom-free RAM compiler. |
| Lean native `mvcgen` | Ordinary result equations or triples, supplied invariants | Semantics of supported Lean computations | No RAM representation or cost theorem follows from the tactic alone. |

### 2.1 Isabelle: pure time functions and refinement are complementary

`Time_Functions` contains ordinary HOL functions and ordinary proofs: `itrev`
is related to list reversal, then `time_fun itrev` generates a time function
whose equation is proved by list induction. Higher-order operations require
enough value and cost information to account for callbacks. This is useful
interface evidence, but the cited `Time_Manual` explicitly says the framework
is unverified and has no underlying formal model. Its general
`time_function` examples can require a separate termination proof for the
generated time function. It is not evidence that cost correspondence or
termination transport comes automatically with native syntax.[^2][^3]

Sepref offers a different experience. In its binary-search quickstart, the
abstract specification uses sorted lists and membership; the author supplies
an interval invariant, a decreasing measure and ordinary list mathematics.
`refine_vcg` handles algorithm verification, and `sepref_definition` produces
an array implementation with a refinement theorem. Composition reuses that
theorem rather than asking for another array-loop correctness proof. The
proof still has a refinement interface: its achievement is hiding routine
representation reasoning, not turning every effectful program into a naked
function equation.[^4]

The 2022 timed-refinement development strengthens the comparison materially.
It connects abstract resource reasoning to a costed LLVM semantics and
synthesizes implementations, including introsort and amortized dynamic-array
operations. It allows correctness and cost to be proved separately before
combination, and its unlimited-credit correctness interpretation still
requires successful termination. However, the paper leaves verified
machine-code compilation and peak-heap analysis as further work. The relevant
lesson is compositional refinement to a declared endpoint, not the inheritance
of its endpoint by another backend.[^5]

**Design implication.** Native equations are valuable for pure functions;
contracts and data refinement are the common composition mechanism. Requiring
every mutable loop to become a separate pure recursive algorithm first would
lose an important benefit of the refinement approach.

### 2.2 CFML: mathematical contracts, frames and callable asymptotic bounds

In the fixed CFML2 tutorial, `repeat_incr_spec` proves a recursive reference
update using a well-founded induction, `xcf`, `xapp` and arithmetic. The
nonnegative-input premise matters: an earlier attempted statement in the same
file is aborted. Another completed example increments one reference while
preserving another with a short `xcf; xapp; xsimpl` proof. Its separating
precondition supplies distinct owned cells; the tactic does not establish
unconditional no-aliasing.[^6]

The implementation of `xapp_lemma` applies a proved ramified-frame rule to a
callee triple and the remaining continuation. This is a concrete example of
the automation Complexity needs: use the selected contract, preserve unrelated
resources, and pass the actual returned value and updated contents forward.
It does not require clients to manipulate an entire heap transformer.[^7]

The older `coq-bigO` artifact packages a usable budget function with its
program specification and mathematical properties in `specO`. Clients can
invoke this function without exposing its coefficients. Its completed
`length2_spec_bigO` composes two list-length calls; the paper's filter/length
example uses a property of the actual intermediate list before simplifying
the cost to an input-size bound. A sufficient monotone budget is not the same
thing as a monotone exact runtime.[^8][^9][^10]

The original union-find time-credit work connects credits to costed source
evaluation, chiefly counting calls, and separates mathematical amortized
analysis from the mutable implementation proof. It does not verify the
subsequent OCaml compiler's machine-cost preservation.[^11] Nor should that
guarantee be assigned wholesale to current CFML2: the inspected snapshot has
an uncosted `hoare` evaluation definition and an admitted record-initialization
axiom elsewhere. Those facts limit claims about the snapshot; they do not
invalidate the usefulness of its proved frame rule or the separately
published costed logic.[^12]

**Design implication.** Reuse mathlib asymptotics, but publish a concrete,
callable upper-bound function alongside the mathematical contract. First
improve existing contents/frame rules; importing an entire separation-logic
implementation is not a prerequisite.

### 2.3 CakeML: native proofs, real mutation and a separate space theorem

The pure translator example translates existing HOL definitions of partition
and quicksort, produces evaluation certificates, and reuses the HOL library's
permutation and sortedness results. The target code is generated from the
function definition, not supplied as a second hand-written algorithm. The
resulting theorem refers to actual CakeML evaluation.[^13]

The monadic translator handles effects through proved correspondence to
native target operations. Its treatment of state-dependent recursion carries
the actual intermediate state into recursive reasoning. It can encapsulate
local state and connect an effectful implementation to a pure interface;
this is a substantive translation result, not simply a monad type alias.[^14]

The current array-quicksort example makes the boundary concrete. It allocates
an array, copies the input list into it, performs mutable quicksort, and reads
the result into a list. The final theorem uses list permutation and sortedness.
This demonstrates pure external behavior with real internal mutation, but
also exposes genuine initialization and conversion work that a complexity
theorem must count. It is not automatic replacement of an arbitrary pure
sorting algorithm by an in-place one.[^15]

CakeML's characteristic-formula tutorial also returns a newly allocated byte
array with an array-contents assertion. That is a mutable result resource,
not a heap-independent list. The two interfaces should remain distinguishable
in Complexity as well.[^16]

The compiler's ordinary correctness theorem permits resource-limit early
exit. Its stronger `compile_correct_safe_for_space` removes that allowance
under an additional space-safety condition.[^17] The space work connects
analysis to compiled representations, actual stack-frame sizes and garbage
collection; its analysis level is below the original source and is not an
automatic high-level time analysis. The cited evidence supplies no general
native-function-to-machine-time bound.[^18]

**Design implication.** Generate translation certificates and pure/effectful
bridges, but retain an explicit resource-adequacy theorem. Source totality
alone cannot rule out target memory exhaustion.

### 2.4 Rocq: a native frontend is feasible, but its scope matters

Forster and Kunze's certifying extraction connects supported ordinary Coq
functions to a call-by-value lambda calculus. Its `computable` interface stores
extracted code and a logical-relation proof; `computableTime` adds a time
bound. Automation generates recurrence constraints, while the author supplies
their solution. The `map` treatment includes callback costs. This is a direct
precedent for a restricted, proof-producing frontend, with the explicit
qualification that its counted reductions and Scott-encoded data are not
word-RAM operations.[^19]

The larger CertiRocq/MetaRocq route addresses a much broader compilation
problem. The official pipeline records quotation and verification boundaries;
it must not be summarized as an entirely verified resource-preserving pipeline.
There is also a version discrepancy: the March 2026 wiki labels direct ANF
translation as proof work in progress, whereas a February 2026 paper gives a
terminating whole-program ANF correctness result. The paper result is evidence;
its exact integration in the inspected main branch remains unestablished.[^20][^21]

The verified CertiCoq-Wasm backend described in CPP 2025 uses monotonically
growing allocation without reclamation, and its theorem permits an
out-of-memory result. That is a precise, useful allocator boundary rather than
a full GC or an unconditional total-program theorem.[^22] Separately, the
space-safe closure-conversion paper proves a particular transformation in
profiling semantics; its theorem relating idealized GC to a real two-semispace
collector is explicitly not mechanized in Coq. A verified transformation
should not be advertised as a verified resource bound for the whole
compiler/runtime chain.[^23]

**Design implication.** Accepting all elaborated Lean terms would be a major
new project. A supported fragment with kernel-checked per-declaration
certificates is a credible route. Unsupported execution constructs should be
reported, not accepted as arbitrary host callbacks with invented prices.

### 2.5 F*/Pulse: hide effects through elaboration, not through omission

The indexed-effects work provides a particularly relevant construction.
Its `Write` effect carries an abstract specification together with an
implementation indexed by that specification. `reify_spec` and `reify_impl`
observe the same effectful program; an outer effect handles framing. Clients
write the operation sequence once while the library handles buffers, offsets
and proof obligations. The two semantic components are not two separately
maintained client algorithms.[^24]

Pulse's reference and array interfaces distinguish scoped local variables,
borrowed access and explicitly allocated containers. Scope exit requires the
appropriate ownership resources; it is not permission to return a reference
to storage that has been reclaimed. Contents are related to mathematical
sequences, while write permissions and alias conditions remain real proof
obligations.[^25]

The official majority-vote example has one mutable implementation and a
mathematical specification using occurrence counts. Two loop invariants
describe the processed prefix; the input array is preserved. The associated
C file contains direct array access, local variables and loops. This is
evidence of the desired programming/verification organization, not of a
machine-cost theorem: no such theorem is in this example. Its generated C
records F* `e4cdebfa` and KaRaMeL `5c7ac22a`, so it should be treated as a
specific tutorial snapshot.[^26][^27]

Two boundaries are essential. The general Pulse logic described in the
official loop tutorial is partial correctness; an intentionally diverging
counterexample satisfies its conditional postcondition.[^28] PulseCore's
later credits support a step-indexed logic, not an algorithmic time budget,
and the paper includes native compilation in its trusted base.[^29]

**Design implication.** Borrow the separation between user syntax, mathematical
specifications and library-managed resources. Do not inherit partial
correctness or treat logical credits as measured RAM instructions.

### 2.6 CALF and Decalf: cost cannot be a property of extensional equality

CALF separates behavior from cost-sensitive computation. A behavioral equality
can relate algorithms with different costs because it is not equality in the
cost-sensitive interpretation. Its recursion discussion includes both
accessibility and clock-based approaches; the framework is not an argument
that every public algorithm must expose a time budget.[^30]

The actual Agda implementation matters. `Calf.CBPV` and `Calf.Step` use
postulates and rewrite laws to embed the logical framework. This is not an
axiom-free implementation of a Lean RAM semantics. Importing the notation or
adding an unrestricted `step` primitive would not transfer its model or
prove that a chosen price matches a target operation.[^31]

The sequential merge-sort split module traverses and reconstructs a list but
proves zero cost under its comparison-counting model. The merge-sort module
also uses an explicit recursion clock and separate valuable-result and cost
proofs. These are concrete reasons not to promise a frictionless ordinary
Lean proof workflow merely by adopting CALF's vocabulary.[^32][^33]

Decalf generalizes bounds to comparisons between effectful programs, preserving
the behavior needed to compose subsequent computation.[^34] In the Agda
global-state example, the bound still reads the initial state and performs the
corresponding update; it does not replace an effectful continuation by a
state-independent number.[^35]

**Design implication.** Keep cost inaccessible to executable control flow,
retain implementation identity, and let resource continuations depend on
actual results and state. These principles can be realized with ordinary Lean
definitions and proved execution relations; a new modal type theory is not
required for the current deterministic backend.

### 2.7 Lean already supports part of the desired proof experience

The official `mvcgen` tutorial proves a plain equation for an `Id.run` array
sum with mutable local syntax. A bridge moves the equation into WP reasoning,
then a supplied mathematical invariant and automation discharge the loop.
It also compares this with a similarly short ordinary fold proof. The point
is a choice of proof method, not that all programs should be proved by VCG.
Neither method supplies a different runtime's representation or cost
correspondence.[^36]

Version discipline matters. The pinned `v4.28.0-rc1` already defines separate
`WP` and `WPMonad` classes; it would be incorrect to claim that only a later
release introduced any such separation.[^37] The 4.33 release documents
support for non-monadic embedded programs in the newer proof infrastructure,
and a frame facility for the newer `vcgen`. These changes are evidence to
consider when designing compatibility boundaries, not permission to assume
those APIs exist at the pin or to upgrade the repository.[^38]

## 3. Recommended architecture

The remainder of this report is design analysis and recommendation. It does
not assert that the proposed interfaces or metatheorems are already available.

### 3.1 One implementation, several justified observations

Initially, one supported high-level declaration should be the canonical
algorithm source. Its elaboration produces the independent typed core and
the evidence connecting supported public observations to that core. For the
pure fragment it also produces an executable total Lean definition and its
equations. Accepting pre-existing Lean definitions through certifying
translation can later be another entry point; it must not introduce a second
semantic authority or an unchecked escape into arbitrary Lean computation.
This is initially a declaration-first frontend with ordinary Lean function
outputs and proofs, not a claim that existing native definitions are already
accepted as inputs. A restricted native-definition entry point remains a
separate frontend capability: its acceptance gate is translation and terminating
correspondence for a supported existing definition without another user body.

An implementation identity is required independently of its extensional
meaning. It need not be a hash, manifest or new registry. The actual Lean
declaration, core term and emitted code, linked by theorem parameters, suffice.
Two programs that both sort correctly are allowed to have different cost
theorems. Replacing one implementation by another requires a new or transported
implementation certificate, not rewriting the cost theorem using function
extensionality.

The basic relationship is:

```text
                         mathematical specification
                                  ↑ proof
one high-level declaration ──→ public function / contents contract
             │                         │ proved correspondence
             └──────────────→ independent typed core
                                        │ verified lowering
                                        ↓
                              register IR → word-RAM code
                                        ↑
                       bounds on that code's actual execution
```

The diagram is not a proposal to maintain two algorithms. Native equations,
syntax and proof views must come from the supported declaration or from a
proved generic transformation of it. A mathematical specification may be
independently stated and need not be executable.

### 3.2 Two proof modes, one composition layer

For pure supported functions, the desired statement really is an ordinary
equation, such as `factorial n = Nat.factorial n`. Equation lemmas, induction
principles and ordinary mathlib reasoning should be the default. A
noncomputable `Part.get` projection obtained only after the full desired
correctness proof does not deliver this programming experience.

For borrowed mutable operations, the desired statement relates initial and
final mathematical contents, the result, and permitted updates. The author
should see a named array or sequence and a mathematical invariant, not the
whole heap. The library must retain the heap relation internally, because
contents observed before a call are not automatically contents after it.
Overlapping views remain meaningful; independent resources require proved
separation, while intentional sharing may be encapsulated in one abstract
data-structure invariant.

These are different proof modes, not an assertion that switching between a
persistent functional algorithm and an in-place one only changes an annotation.
If such a switch changes data sharing or the algorithm, a real verified
transformation is required. Otherwise it is a different implementation.
Ordinary mutation syntax must not silently authorize destructive updates to
an old persistent value that remains observable.

The shared contract layer should handle calls, actual intermediate results,
representation facts, input retention or consumption, output relations and
frames. A pure contract embeds into this layer without inventing heap effects.
An effectful contract can expose a pure mathematical observation only when the
corresponding abstraction theorem applies. Existing source imports and old-IR
bridges should consume these contracts rather than create competing ones.

### 3.3 Termination is supplied once, transported many times

The correct promise is not that a single theorem magically proves every layer.
It is that the author does not repeat the same termination argument in each
layer. A pure recursive declaration supplies structural descent or a
well-founded argument. Generated correspondence uses generic recursion rules
and must establish an actual finite core execution, not only equality of
results when execution happens to terminate.

There is a concrete hook at the existing Lean pin: `getFunIndInfo?` exposes
argument routing for a generated functional induction theorem, including its
`induct_unfolding` variant. The derivation handles structural and well-founded
definitions.[^39] Use that checked recursion structure with the motive
`forall heap, sourceAction args heap = some (ok (nativeFunction args), heap)`.
The generated proof discharges each branch using the source-body equation,
callee correspondence and the supplied recursive hypotheses. This is a design
for proof-producing elaboration, not an assumption that the two generated
functions agree. It reuses the author's termination argument without trying to
infer the algorithm's mathematical specification or RAM range/capacity bounds.

Declared domains must be explicit. When termination is known only under
`Pre x`, the default total interface should take a domain subtype or a proof
argument; an executable domain check may instead produce an explicit error
result. A total extension outside the domain is acceptable only if its behavior
is genuinely defined and its correspondence theorem states the domain
restriction. A default value projected from an unsuccessful partial computation
does not supply such an implementation.

For a mutable loop, the author supplies a state invariant and a variant over
the state actually observed at the loop boundary. An effectful guard may
change the heap; a recursive callee may change facts needed by its continuation.
The contract generator must pass these actual states through its rules.
Reusing an unrelated mathematical function's termination proof does not prove
termination of this loop.

Numeric width, stack capacity and heap capacity belong to target realizability.
They should reuse shape/range facts from correctness, but they are not a
source time budget. A compiler pass that introduces additional computation
must prove that computation terminates too. If a later optimization changes
the recursive structure, additional internal proof obligations are legitimate;
they should be solved generically when possible, not hidden by a partial
correctness theorem.

### 3.4 A concrete first allocation and return protocol

For the first allocating fragment, use a stable-address, bounded arena whose
lifetime is owned by the surrounding evaluation session or caller. Allocation
progress is shared across nested calls, not stored in caller locals that are
restored on return. Returned buffers refer to this still-live arena. A function
return does not reset it. The initial guarantee concerns cumulative allocated
words and capacity, not reclaimed or peak reachable space.

This protocol allows a function to allocate, initialize and return a new
container; a following call can use it, and further allocation must preserve it.
It is not merely a caller-preallocated output buffer. The low-level caller
provides an arena resource, while a higher-level execution boundary may arrange
that resource without exposing pointer arithmetic to algorithm authors.

The first implementation may omit arena reset entirely. That is an explicit
restriction, not a claim of automatic collection. Scoped scratch regions are
the next extension: reset requires a proof that no live result, borrowed
handle or stored reference can reach reclaimed storage. Returned owned data
must be placed in a longer-lived region, transfer a region's ownership, or be
copied out by an implemented and charged operation. The library must choose
one policy for each API rather than mixing these cases implicitly.

Allocation also requires initialized cells, valid-address transport, and a
fresh-object policy compatible with existing handles. The current public
buffer type permits nonexistent object IDs; merely appending a heap object
could turn a formerly invalid handle into a valid one while leaving an old
RAM descriptor stale. New allocation-aware contracts must establish live
handle validity and stable encodings. Existing no-allocation theorems should
remain available without silently strengthening all their premises.

For the first scalar-array fragment, permissions can be expressed using
intervals, contents and existing frame relations. Future pointer-bearing
containers need representation of their reachable graph. Returning two aliases
of one buffer must not grant two independent write permissions. A freeze
operation needs the absence of surviving writable aliases; a pure snapshot
requires a real copy unless a proved ownership transfer makes copying
unnecessary. These are semantic obligations, not reasons to ban all aliasing.

Finite-memory failure needs a deliberate interface. Initially, retain the
current separation: abstract source allocation with fresh initialized storage,
and a target-success theorem under a sufficient-capacity premise. Do not claim
the target implements an out-of-memory exception until such behavior is
specified and compiled. If fallible allocation is later made public, its
failure contract must account for retained ownership and any earlier effects.

### 3.5 Pure results from private mutation

A public mathematical result can hide local state, but two distinct guarantees
are needed. First, different representations of the same mathematical input
must produce corresponding results: selecting one empty or convenient heap
does not prove representation independence. Second, the returned value's
observable contents must survive subsequent legal uses. The absence of writes
in the current function proves neither property by itself.

Here the two result interfaces must be precise. A mutable return guarantees
contents at the return boundary; a later permitted write changes the contents
relation. A persistent pure return must instead use an immutable/shared
representation, or a verified usage discipline that preserves every observable
old version, copying when necessary and charging for it. Exclusive ownership
transfer and a longer arena lifetime prevent some alias/lifetime failures, but
alone do not make a writable result a persistent pure value.

A same-declaration pure view can be generated for a supported local-state
fragment using an ordinary total mathematical state interpretation, then
related to the actual mutable core by a generic simulation. This remains a
future construction. The mathematical view may use persistent Lean arrays
internally without implying that the RAM program executes those host updates.
Conversely, a Lean array equation alone does not justify a destructive RAM
update; the representation and usage proof must justify it.

Until this bridge exists, publish honest contents contracts for mutable
results, not a cosmetically pure wrapper. However, contents contracts are not
the final replacement for the requested executable pure interface. The
roadmap must retain both capabilities and require evidence for their bridge.

### 3.6 Cost and space over the same execution

Functional correctness, numerical cost reasoning and compiler adequacy should
remain separate proofs that compose. Exact operation costs belong in backend
rules. Public contracts should usually export upper bounds whose constants
are hidden, together with useful shape facts. Clients may then use mathlib
sums, recurrences, potentials and `IsBigO` without opening ABI definitions.

A sequential rule must account for the real intermediate result and state.
Schematically, if the first call returns `(y, h')`, the second bound is
`B₂ y h'`, not a bound evaluated at the original heap. Only a proved shape
property and suitable monotonicity or pointwise domination can replace this
by an input-size-only expression. Monotonicity can be required of a chosen
upper-bound function; it should not be imposed on exact runtime.

The final theorem must combine successful source termination, target
realizability and a bound for the same emitted code. In schematic mathematics:

```text
algorithm precondition ∧ valid representation ∧ legal word ranges ∧ capacity
    ⇒ ∃ finite RAM execution of this declaration's code,
         successful return ∧ specified result/effects ∧ steps ≤ budget
```

This is not proposed Lean syntax and not an existing theorem name. A
conditional bound over successful executions alone is insufficient: it can be
vacuous when no such execution exists. An out-of-memory exit is not successful
return. Uniform asymptotic claims must quantify the input family, size measure
and width/capacity policy using the existing problem and uniform-time
interfaces.

Space observations need separate meanings. Stack capacity, reserved arena
capacity, cumulative allocation, retained allocated data, and reachable live
data are not synonyms. Current access footprints count addresses visited, not
live objects. The generic prefix/peak framework can support new observations,
but does not supply their lifetime interpretation. Allocation initialization,
copying, reclamation and any later collector must contribute their actual
execution costs.

### 3.7 Automation and reuse boundaries

The first automation work should target generated equation normalization,
typed call contracts, frame/contents transport and loop obligations over named
locals. Arithmetic, list and array reasoning should reuse Lean, Std and
mathlib. Missing glue should be a small proved rule or an adapter over existing
ones, not another evaluator or a new asymptotic library.

The generator should expose failed obligations in mathematical terms: an
index bound, a missing callee precondition, a decreasing measure, or an alias
condition. It should not guess away a safety condition. Algorithmic invariants,
potential functions and nontrivial recurrence solutions remain author work;
the aim is removing administrative proofs, not claiming to solve arbitrary
program verification automatically.

A backend maintainer still needs register, call/return, layout and simulation
lemmas. Hiding those from algorithm clients does not make their maintenance
irrelevant. Old DSL theorem reuse belongs in the connection layer and requires
correspondence to the selected implementation, especially for cost transport.

## 4. Alternatives and decision boundaries

A universal `ExceptT/StateT/Part` public interface preserves expressive
semantics but makes pure proofs pay for irrelevant representation details.
Keeping it internally is sensible; requiring clients to manipulate it is not
the target experience.

A universal native-function-first architecture makes scalar examples pleasant,
but does not by itself handle borrowed mutation, lifetime or efficient data
refinement. It can also duplicate termination and algorithm definitions if
correspondence is left to clients. The pure-function proof interface is selected
for the supported pure path, initially via a single high-level declaration that
generates its native view. It is not the prerequisite for every effectful proof,
nor a claim that a native-definition input frontend is already implemented.

A full compiler for arbitrary Lean, or an immediate GC runtime, could support
broader programming patterns. Neither is needed to establish the required
first interfaces, and neither should be treated as a small extension of the
current core. These remain scope decisions, not capabilities implicitly
inherited from other proof assistants.

A literal port of CALF would add a logical framework and its metatheory while
leaving the chosen RAM connection to prove. A bare writer-style cost wrapper
would be smaller but could leave exactly the same gap. The recommended design
uses the existing counted execution and adopts only the justified interface
principles.

The principal unresolved technical questions are the implementation of shared
recursive correspondence, executable pure observations for the local-state
fragment, and allocation-aware handle/lifetime invariants. The architectural
direction does not count these as solved. Before expanding syntax, each needs
a concrete theorem shape against an existing consumer or the first genuine
allocating consumer.

## 5. Roadmap consequences

Keep the existing typed core, compiler, import transport and measured execution.
Reorder the frontend work around shared contracts and complementary proof
modes. The pure-function milestone and mutable-loop milestone proceed in
parallel; allocator/return protocol design is not postponed until every scalar
proof is polished. Richer products, tagged results and collection operations
remain necessary for a usable language.

| Capability gate | Required evidence | Insufficient substitute |
| --- | --- | --- |
| Pure functions | One supported declaration gives an executable total function, ordinary equations and generated terminating core correspondence | A result projection requiring the old full action proof |
| Mutable proofs | Existing traversal and imported callers use contents invariants, real descent and automatically transported frames | A short theorem hiding an equally long private adapter |
| Fresh containers | Allocation, initialization, return, subsequent use and further allocation preserve the live result and have actual costs | A host-created output buffer or heap-append lemma |
| Private-state abstraction | The same body obtains an executable pure view with representation independence, lifetime safety and preservation of observable old values | Erasing the heap parameter, or calling a writable return value persistent |
| Published complexity | A mathematical bound composes into successful execution of the same RAM code under explicit legal-input conditions | Ghost ticks, source-call counts or an existential fast implementation |
| Space reclamation | A real release/reset operation, non-escape proof and counted implementation | Dropping a logical assertion or decreasing a ghost counter |

These are proof obligations and review consumers, not a request for a new test
framework. The complete proof should be reviewed for duplicated reasoning and
changed assumptions. Existing examples are sufficient to drive the first
interface work; new algorithm collections would not resolve the current
abstraction gaps.

The recommendation is well-supported as an architecture, but it is not a
claim that one design is universally best. If an intended program requires
cross-region sharing, persistent updates or dynamic higher-order values that
the selected fragment cannot express, the representation and compilation
policy must be reconsidered explicitly. Such evidence should change the
roadmap rather than be hidden behind a simpler replacement problem.

## Sources

[^1]: Complexity, repository baseline `a1e99a9`: [source types](../Complexity/Language/Basic.lean), [heap](../Complexity/Language/Heap.lean), [factorial](../Examples/Language/Factorial.lean), [traversal](../Examples/Language/Traversal.lean), [RAM heap representation](../Complexity/Computability/Ram/Compiler/Language/Heap.lean), and [execution bridge](../Complexity/Computability/Ram/Compiler/Language/Execution.lean).

[^2]: Isabelle/HOL Library, [Time_Functions](https://isabelle.in.tum.de/library/HOL/HOL-Library/Time_Functions.html), online library snapshot, September 2026; `itrev`, `T_itrev` and higher-order examples.

[^3]: Isabelle/HOL Library, [Time_Manual](https://isabelle.in.tum.de/website-Isabelle2025-1-RC3/dist/library/HOL/HOL-Library/Time_Manual.html), Isabelle2025-1-RC3; general recursion, higher-order timing and “Fine Points.”

[^4]: Peter Lammich, [Sepref_Guide_Quickstart](https://isa-afp.org/browser_info/current/AFP/Refine_Imperative_HOL/Sepref_Guide_Quickstart.html), AFP Refine_Imperative_HOL, current online snapshot in September 2026; `in_sorted_list1_refine`, `in_sorted_list2_correct`. No immutable snapshot identifier is asserted.

[^5]: Maximilian P. L. Haslbeck and Peter Lammich, [For a Few Dollars More: Verified Fine-Grained Algorithm Analysis Down to LLVM](https://ris.utwente.nl/ws/files/297739784/3486169.pdf), TOPLAS 44(3), 2022, DOI 10.1145/3486169; §§3–6 and §7.2. The linked [LLVM-Time artifact](https://www21.in.tum.de/~haslbema/llvm-time/) specifies Isabelle2020.

[^6]: Arthur Charguéraud, CFML2 [Tutorial_proof.v](https://github.com/charguer/cfml/blob/4359c19e0eee323bd7b3ce7f43e451bd34440c09/examples/Tutorial/Tutorial_proof.v#L100), commit `4359c19e0eee323bd7b3ce7f43e451bd34440c09`, March 2025; `incr_one_of_two_spec`, completed `repeat_incr_spec`.

[^7]: Arthur Charguéraud, CFML2 [WPTactics.v](https://github.com/charguer/cfml/blob/4359c19e0eee323bd7b3ce7f43e451bd34440c09/lib/coq/WPTactics.v#L1609), same commit; `xapp_lemma` and `Triple_ramified_frame` application.

[^8]: Armaël Guéneau et al., coq-bigO [CFMLBigO.v](https://gitlab.inria.fr/agueneau/coq-bigO/-/blob/1fd4e6e435a7ed54e52fb40450f516cfd46aeb14/src/CFMLBigO.v#L27), commit `1fd4e6e435a7ed54e52fb40450f516cfd46aeb14`, December 2019; `specO`.

[^9]: Armaël Guéneau et al., coq-bigO [Composing_specs.v](https://gitlab.inria.fr/agueneau/coq-bigO/-/blob/1fd4e6e435a7ed54e52fb40450f516cfd46aeb14/examples/proofs/Composing_specs.v#L102), same commit; `length2_spec_bigO`.

[^10]: Armaël Guéneau, Arthur Charguéraud and François Pottier, [A Fistful of Dollars: Formalizing Asymptotic Complexity Claims via Deductive Program Verification](https://armael.deuxfleurs.page/publis/gueneau-chargueraud-pottier-coq-bigO.pdf), 2018; §§4.5–5.

[^11]: Arthur Charguéraud and François Pottier, [Verifying the Correctness and Amortized Complexity of a Union-Find Implementation in Separation Logic with Time Credits](https://www.chargueraud.org/research/2017/credits_jar/credits_jar.pdf), author's 2017 manuscript for the JAR article; Definition 2 and §§2.6–2.7. [Implementation archive](https://gallium.inria.fr/~fpottier/dev/uf/), published for Coq 8.5, is a separate historical artifact.

[^12]: CFML2, [SepBase.v](https://github.com/charguer/cfml/blob/4359c19e0eee323bd7b3ce7f43e451bd34440c09/lib/coq/SepBase.v#L497) and [WPValid.v](https://github.com/charguer/cfml/blob/4359c19e0eee323bd7b3ce7f43e451bd34440c09/lib/coq/WPValid.v#L555), commit `4359c19e0eee323bd7b3ce7f43e451bd34440c09`; `hoare` and `triple_record_init`. These delimit this snapshot, not all CFML versions.

[^13]: CakeML, [ml_translator_demoScript.sml](https://github.com/CakeML/cakeml/blob/e6bb97e7b11423ddb00b92e00b7dc972de361e89/translator/ml_translator_demoScript.sml), commit `e6bb97e7b11423ddb00b92e00b7dc972de361e89`, September 2026; generated quicksort certificates and `ML_QSORT_CORRECT`.

[^14]: Oskar Abrahamsson, Son Ho, Hrutvik Kanabar, Ramana Kumar, Magnus O. Myreen, Michael Norrish and Yong Kiam Tan, [Proof-Producing Synthesis of CakeML from Monadic HOL Functions](https://research.chalmers.se/publication/518990/file/518990_Fulltext.pdf), JAR 64, 2020, DOI 10.1007/s10817-020-09559-8; §§4–5.

[^15]: CakeML, [poly_array_sortProgScript.sml](https://github.com/CakeML/cakeml/blob/e6bb97e7b11423ddb00b92e00b7dc972de361e89/translator/monadic/examples/poly_array_sortProgScript.sml#L990), same CakeML commit; `quicksort`, `run_quicksort`, translation commands and `qsort_thm`.

[^16]: CakeML, [cf_tutorialScript.sml](https://github.com/CakeML/cakeml/blob/e6bb97e7b11423ddb00b92e00b7dc972de361e89/characteristic/examples/cf_tutorialScript.sml#L193), same commit; allocated byte-array result and `W8ARRAY` contract.

[^17]: CakeML, [compilerProofScript.sml](https://github.com/CakeML/cakeml/blob/e6bb97e7b11423ddb00b92e00b7dc972de361e89/compiler/proofs/compilerProofScript.sml#L232), same commit; `compile_correct_safe_for_space` and `compile_correct`.

[^18]: Alejandro Gómez-Londoño, Johannes Åman Pohjola, Hira Taqdees Syeda, Magnus O. Myreen and Yong Kiam Tan, [Do You Have Space for Dessert? A Verified Space Cost Semantics for CakeML Programs](https://cakeml.org/oopsla20.pdf), OOPSLA 2020, DOI 10.1145/3428272; §§2 and 7. Current implementation: [backendProofScript.sml](https://github.com/CakeML/cakeml/blob/e6bb97e7b11423ddb00b92e00b7dc972de361e89/compiler/backend/proofs/backendProofScript.sml#L2713).

[^19]: Yannick Forster and Fabian Kunze, [A Certifying Extraction with Time Bounds from Coq to Call-By-Value λ-Calculus](https://www.ps.uni-saarland.de/Publications/documents/ForsterKunze_2019_Certifying-extraction.pdf), ITP 2019, DOI 10.4230/LIPIcs.ITP.2019.17; §§4.5–5.4. [Official implementation](https://github.com/uds-psl/certifying-extraction-with-time-bounds).

[^20]: CertiRocq project, [The CertiRocq pipeline](https://github.com/CertiRocq/certirocq/wiki/The-CertiRocq-pipeline), wiki revision dated March 19, 2026. A project status page, not a resource-preservation theorem.

[^21]: Zoe Paraskevopoulou, [Machine-Generated, Machine-Checked Proofs for a Verified Compiler (Experience Report)](https://arxiv.org/html/2602.20082v1#S4.SS2), arXiv:2602.20082v1, February 23, 2026; Corollary 4.2 on terminating whole-program ANF correctness. Main-branch integration is not established here.

[^22]: Wolfgang Meier, Martin Jensen, Jean Pichon-Pharabod and Bas Spitters, [CertiCoq-Wasm: A Verified WebAssembly Backend for CertiCoq](https://www.cl.cam.ac.uk/~jp622/certicoq-wasm.pdf), CPP 2025, DOI 10.1145/3703595.3705879; §2.1.1 and Theorem 2.1.

[^23]: Zoe Paraskevopoulou and Andrew W. Appel, [Closure Conversion Is Safe for Space](https://www.cs.princeton.edu/~appel/papers/safe-closure.pdf), ICFP 2019, DOI 10.1145/3341687; §5, Theorem 5.1 and its explicit mechanization boundary.

[^24]: F* project, [Programming and Proving with Indexed Effects](https://www.fstar-lang.org/papers/indexedeffects/indexedeffects.pdf), technical report, 2021; §5, `Write`, `FWrite`, `reify_spec`, `reify_impl`.

[^25]: F* project, [Mutable References](https://fstar-lang.org/tutorial/book/pulse/pulse_ch2.html) and [Mutable Arrays](https://fstar-lang.org/tutorial/book/pulse/pulse_arrays.html), official Pulse tutorials, online snapshot in September 2026.

[^26]: F* project, [PulseTutorial.Algorithms.fst](https://github.com/FStarLang/pulse-tutorial-24/blob/main/tutorial/PulseTutorial.Algorithms.fst), POPL 2024 tutorial repository; `majority` and `majority_mono`.

[^27]: F* project, [PulseTutorial_Algorithms.c](https://github.com/FStarLang/pulse-tutorial-24/blob/main/tutorial/PulseTutorial_Algorithms.c), associated tutorial-generated output; header records F* `e4cdebfa`, KaRaMeL `5c7ac22a`.

[^28]: F* project, [Loops & Recursion](https://fstar-lang.org/tutorial/book/pulse/pulse_loops.html), official Pulse tutorial, online snapshot in September 2026; partial correctness and `count_down_loopy`.

[^29]: F* project, [PulseCore paper](https://fstar-lang.org/papers/pulsecore-indirection-2025.pdf), PLDI 2025; §§4.1–4.2, later credits and native-compilation trust boundary.

[^30]: Yue Niu, Jonathan Sterling, Harrison Grodin and Robert Harper, [A Cost-Aware Logical Framework](https://arxiv.org/abs/2107.04663), POPL 2022; cost/behavior distinction and §1.6 on recursion.

[^31]: CALF project, [Calf.CBPV](https://github.com/calfproject/agda-calf/blob/main/src/Calf/CBPV.agda) and [Calf.Step](https://github.com/calfproject/agda-calf/blob/main/src/Calf/Step.agda), `main` source snapshot in September 2026; postulates and rewrite laws.

[^32]: CALF project, [MergeSort.Split](https://github.com/calfproject/agda-calf/blob/main/src/Examples/Sorting/Sequential/MergeSort/Split.agda), same source snapshot; `split/clocked`, `split/cost`, `split/is-bounded`.

[^33]: CALF project, [MergeSort](https://github.com/calfproject/agda-calf/blob/main/src/Examples/Sorting/Sequential/MergeSort.agda), same source snapshot; `sort/clocked`, `sort/clocked/total`, `sort/clocked/is-bounded`.

[^34]: Harrison Grodin, Yue Niu, Jonathan Sterling and Robert Harper, [Decalf: A Directed, Effectful Cost-Aware Logical Framework](https://arxiv.org/html/2307.05938v4), arXiv revision May 20, 2026, following the POPL 2024 publication; §§1.3–1.5 and 3.2. This revision is distinguished from the January 2024 version.

[^35]: CALF project, [Examples.Decalf.GlobalState](https://github.com/calfproject/agda-calf/blob/main/src/Examples/Decalf/GlobalState.agda), `main` source snapshot in September 2026; `StateDependentCost.e`, `e/bound`, `e/has-cost`.

[^36]: Lean project, [Verifying Imperative Programs Using mvcgen](https://lean-lang.org/doc/tutorials/latest/mvcgen/), official online tutorial, September 2026; `mySum`, equation-to-WP bridge and invariant-based proof.

[^37]: Lean project, [Std.Do.WP.Basic](https://github.com/leanprover/lean4/blob/v4.28.0-rc1/src/Std/Do/WP/Basic.lean) and [Std.Do.WP.Monad](https://github.com/leanprover/lean4/blob/v4.28.0-rc1/src/Std/Do/WP/Monad.lean), pinned `v4.28.0-rc1`; class definitions also inspected in the installed source.

[^38]: Lean project, [Lean 4.33.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.33.0/), August 10, 2026; changes #14080, #14146 and #14167. These are not APIs claimed available at Complexity's pin.

[^39]: Lean project, [FunIndInfo](https://github.com/leanprover/lean4/blob/v4.28.0-rc1/src/Lean/Meta/Tactic/FunIndInfo.lean) and [FunInd](https://github.com/leanprover/lean4/blob/v4.28.0-rc1/src/Lean/Meta/Tactic/FunInd.lean), pinned `v4.28.0-rc1`; `getFunIndInfo?`, argument routing, and `deriveInduction` for structural/well-founded definitions. Official source and installed pinned source inspected.
