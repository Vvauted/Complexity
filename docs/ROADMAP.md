# Roadmap

The goal is to write a program once, with its result and execution cost as properties
of that same program, and prove them using ordinary Lean mathematics. Reusable
functions are the primary unit: a function should not need an input/output `main`
to be defined, called or verified. This roadmap closes the gap between that
functional-programming experience and the interfaces available today.

## Where we are

The word-RAM backend already has a structured source language, named locals and
functions, recursive calls, verified compilation and executable runners.
Budget-free total correctness, separate time bounds, mathematical refinement
and bridges to native `StateM` verification are implemented.

Function-only declarations generate typed argument lists and `eval`, `bodyTime`,
`run`, `runTotal`, `apply` and `applyState` entry points. Declared word or array
parameters come first, followed by heap capacity and caller state; the last three require
a normal-halt proof. No input/output `main` is required. Return values,
shared effects and body counts are observations of the existing execution, with
actual call overhead added at call sites. Factorial, array-copy and array-sum
expose this interface. A graph-degree client reuses the
sum contract and mathlib's `SimpleGraph.degree` without register or stack proofs.
Array sum, occurrence counting and the call-based sum of squares share cursor
progress, termination, framing and compiler-derived loop costs. A fold step can
be a read-only source expression or a real call to an already proved function.
The call-based exact-count rule currently requires a constant callee-body count.
Lexical `let`, `let mut` and call-result bindings allocate locals at their
declaration sites. Scoped `call f(...);` and `let _ ← call f(...);` discard a
returned word without a dummy source binding, retaining its actual call and effects.
The private destination still contributes to the inferred frame and cost;
`Unit` return signatures are not implemented. Scoped `for x in xs` binds each loaded
element and manages private cursor locals. Source-derived function rules infer
those locals from generated body and return equations for expression updates and
fixed helper calls.
The expression rule retains the array descriptor and all additional word parameters;
sum and count need no hand-written cursor or target-preservation invariant.
Clients still prove the expression's read safety and evaluation, or supply the
actual helper's contract, together with the array representation premises.
Factorial's main correctness proof directly inducts on its argument/result
contract using ordinary natural-number induction and the existing parameter
verification rules. More general clients and the remaining low-level adapters
still show why the source-facing work below is unfinished.

`Func.eval` and `Func.bodyTime` expose the same execution through mathlib's `Part`.
The factorial function-value sample states result equations and mathematical
properties without carrying source state in each proposition. These remain
noncomputable semantic observations, distinct from executable ordinary application.
The compiled function-call adapter additionally executes intermediate functions
without a stream driver, using runtime word arguments and a preloaded shared state.
Its correctness bridge needs no time budget. `Function.runUntil` executes the same
call until it stops, with no supplied instruction limit; `Function.run` retains a
limit for interruptible exploration. Both are connected to actual machine traces,
returned values and exact counts, under code and stack representability premises.
A divergent unbounded call keeps running; the interface does not decide termination.
An exact runner theorem can combine a function's correctness proof with a separate
equation for its body-time observation. A shared generated-code-length lemma handles
outer call overhead, rather than repeating frame arithmetic in each runtime client.

Ordinary application uses `runTotal`, `apply` and `applyState` on this same compiled run.
Their `Halts` proof establishes a returned result with reason `halted`, not merely
an `isSome` result that could be a fault. `runTotal` extracts the actual `Option`
output and retains state and steps; `apply` projects its returned word, and
`applyState` also recovers reusable source shared state without private stack cells.
Proofs are erased at runtime: no mathematical answer or time estimate is passed to the
implementation. The existing factorial and sum clients expose ordinary `Nat`
results with separate value and step equations. They execute with `#eval`, not by
making `Part` computable or compiling arbitrary Lean functions. Their fixed word
width, stack-capacity and preloaded-data premises remain explicit; proofs use the
execution equations rather than expecting kernel computation by `rfl`.

Named functions accept array parameters as well as words: `fn sum(xs : array)`
and `call sum(xs)` pass a by-value base address and length through the existing ABI.
`ArrayRef.Rep` connects that reference to an ordinary mathematical list. Sum and
count use this interface; `sumPair` composes two sum calls without reconstructing
their loops or frames. Typed local handles can alias an existing array, construct
`array(base, length)` or borrow `subslice(xs, offset, count)` into two fresh local
slots. Their descriptor assignments and address arithmetic execute in the same
source program; they neither allocate storage nor copy elements. Array-valued
returns, general typed data values, allocation and automatic loading from Lean
data remain unfinished.

Source declarations can include earlier `ram_def` implementations under aliases.
Stored word/array signatures guide their calls; generated function-table embeddings
transport contracts after linking and relocation. The copy-then-sum source client
uses the existing copy and sum implementations inside one compiled invocation,
with an independent cost proof rather than host-side runner sequencing.
Source-facing time rules infer call arguments and destinations from the generated
body, including discarded results, and reuse correctness postconditions to continue
the separate cost argument on actual shared state. Bounds and reserves remain
proof obligations, not execution fuel or supplied prices.
Assignment and skip prefixes, including the two assignments of a local array
descriptor, are advanced with their compiled costs before those call rules apply.

`TotalComponent` carries that separation through reusable program packaging and
linking. A separate time proof recovers the same code through the resource-aware
component interface; migrating richer data-operation clients remains part of the work below.

The mathematical layer already covers polynomial growth, finite sums,
logarithmic and branching recurrences, Akra–Bazzi and amortized analysis.
Executable component composition, polynomial-time reductions and fixed-problem
certificates also exist. These are RAM results under explicit encoding and
word-width assumptions, not a simulation into a bit-level machine.

The main obstacle is proof composition at the source level. Names currently
resolve to registers, but many proofs still manipulate those registers and
memory layouts. Some examples maintain a named program alongside a separate
AST. Native `mvcgen` verifies mathematical models after an implementation
refinement has been supplied; it does not derive that refinement automatically.

## What the samples tell us

- Mathematical specifications are not restricted to machine objects. The
  graph-degree sample states a standard mathlib graph property and derives it
  from a list-sum contract. Its `sum_eq_degree` also rewrites the ordinary executable
  `ArraySum.sum` value equation to `G.degree v`, without opening an execution
  relation, loop or ABI proof. It assumes a represented adjacency row; it does not
  implement a graph loader or compile a Lean adjacency predicate.
- Reuse can avoid machine-level proofs: the graph client never opens the sum
  loop, register assignments or frame handling. Sum and count now share those
  traversal arguments through the source-derived `ForIn.Expression` rule and its
  shared cursor infrastructure; count's permutation-invariance proof is ordinary
  `List.Perm.count_eq`. The array-sum example reuses the function's value and measured
  execution rather than maintaining a second raw-block loop proof. The reusable
  rules handle one word accumulator with a read-only expression or a fixed verified
  function call, not arbitrary Lean callbacks, short-circuiting or mutable traversals.
- Function-value equations make later mathematical proofs natural, but do not
  make the implementation proof automatic. Semantic `Part` observations and
  executable function application are distinct interfaces, now connected for both
  bounded and unbounded runners. State fields for input and output do not imply
  stream operations: the factorial function contract holds at every caller state
  and proves it unchanged. Its optional `read`/`write` driver lives in a separate
  module importing the function; function definitions and proofs do not depend on
  that adapter.
- Ordinary executable values no longer require a `Part` result type: the factorial
  client proves `factorial_eq_mod`, exact equality and positivity when the result
  fits, while sum proves its ordinary modular list-sum equation. Their definitions
  use the actual generated `apply`, not the mathematical specification. Sum's list
  occurs only in an erased representation/range proof; the runtime inputs are its
  reference, heap boundary and existing state. Independent `runTotal` step equations
  retain `37 * n + 33` for factorial and `18 * n + 67` for sum's full invocation.
- Effectful applications can return usable shared state through `applyState`.
  The copy client states its actual destination contents with `arrayContents` and
  passes that returned state to sum. The shared projection restores caller registers,
  retains actual heap/I/O effects and keeps entry memory outside the heap; it does
  not expose the private target stack. `copyThenSum` sequences two real compiled
  calls in the host language, not one newly compiled RAM program. It has no combined
  full-run RAM-cost theorem and implements no loader.
  A separate conditional body bound gives at most `19 * n + 42` steps for the actual
  single copy invocation, including call and halt, without entering its termination proof.
- Cross-module source calls use `include copyFunctions as Copy` and
  `include sumFunctions as Sum`. The `FunctionComposition` client transports
  their contracts through generated embeddings and calls them from one declared
  `copyThenSum`. Its ordinary result retains the modular sum, copied destination
  and framing; no callee loop is reimplemented. This is a different executable
  composition from `ArrayCopyFunction.copyThenSum`'s two host-level calls.
  Imported aliases retain all six generated interfaces; `imported_sumPair_eval`
  also transports sumPair's existing theorem across its nested sum-call relocation.
  Separate timing bounds the body by `37 * n + 107` and the full invocation by
  `37 * n + 170`, where `n` is the represented list length. These are upper bounds,
  not general exact equalities. The full bound includes both inner calls, the outer
  call and halt, but not host-side heap preloading. The body's separate proof uses
  `ram_time_vc`, `ram_time_apply` and `ram_time_call`; it no longer assembles call
  expressions, names the discarded result slot or writes an intermediate register
  invariant. Generated header equations and proved call-length rules normalize
  actual overhead without expanding callee bodies. The author still supplies the
  callee contracts, array facts and a sufficient bound for the remaining call.
- The recursive factorial contract uses ordinary induction, generated parameter
  binding and the recursive call's argument/result contract. Its algorithmic
  proof names no registers or callee frames. A separate one-step bridge retains
  the stronger body-local endpoint needed by existing time interfaces; that
  endpoint cannot be recovered from a returned value and restored caller state
  alone. Input representability and the factorial equations remain mathematical
  obligations, independent of time bounds.
- The two-argument squared-norm sample composes helper calls with lexical value bindings.
  `ram_total_vc args entry hp` starts its function contract directly; supplied
  call contracts and simplification facts handle the calls without a separate
  intermediate-state specification, register names or stack layouts. The two-array
  sum uses the same rules, reusing each array's representation across scalar-result
  binding. Mathematical preconditions, invariants and contract selection remain
  the proof author's work;
  richer array and recursive clients must reach the same level of convenience.
- The array sum-of-squares sample calls `addSquare`, which calls the same `square`
  used by the two-argument sample. Its proof reuses that contract and an ordinary
  `List.foldl` identity; it never expands the helper's implementation. Its result
  is the encoded natural-number sum of squared decoded words. A separate body
  equation proves `76 * n + 8`, and executable application proves `76 * n + 67`
  including all calls and halt. These are properties of one implementation, not
  supplied results or cost annotations. The source uses `for x in xs`; its
  function proof does not name private cursors, extract call expressions or
  assemble register roles. Descriptor copies, actual element loads and the
  larger local frame all contribute to the count.
- Array arguments remove pointer/length assembly at typed call sites. The
  two-array sample states its result using list concatenation, although the
  program only adds two returned sums and never allocates a concatenated array.
  Read-only references may overlap. Mixed array/word arguments also work for count.
- The local-slice sample writes `let window : array := subslice(xs, offset, count)`
  and calls the imported sum with `window`. Its function contract reuses
  `ArrayRef.Rep.subslice` and sum's existing contract; its result is the ordinary
  list expression `(xs.drop offset.toNat).take count.toNat`. The separate
  `sumSlice_eq` equation exposes that result as an ordinary executable natural
  number modulo the word range. Empty-slice, whole-array and adjacent-partition
  properties then use standard list identities without reopening any execution
  relation. The partition theorem compares returned values, not a newly compiled
  two-call program. The descriptor is borrowed metadata, not a copied array or
  checked slice constructor: containment and no-wrap conditions remain explicit.
  Its independent time proof bounds the body by `18 * count.toNat + 72` and the
  full invocation by `18 * count.toNat + 142`, including descriptor work, calls
  and halt but not host preloading. These are upper bounds, not exact equations.
  General nested array expressions are not implemented; `subslice` starts from
  a bound handle, so construct or slice an intermediate handle with a prior `let`.
- The expression-fold body counts are `18 * n + 8` for sum and `20 * n + 8` for
  count; their executable calls take `18 * n + 67` and `20 * n + 76`, including halt.
  Count's target is a real runtime parameter, not stream input or a proof-only value.
  The pair's cost proof reuses sum's exact count and 58 steps of actual overhead
  per inner call: its body takes `18 * (n + m) + 132`, and its full invocation takes
  `18 * (n + m) + 197`. Descriptor copies, element bindings and enlarged frames are
  charged. These claims concern the represented data, not an unimplemented loader.
- The source-derived traversal rules currently handle an array-first expression
  fold with additional word parameters, or a single-array fold through a fixed
  verified two-argument helper, each with one initialized scalar accumulator.
  The source syntax accepts richer bodies, but their proofs do not yet receive
  the same convenience. Single-step expression proofs still discharge read safety
  and evaluation and may use generated parameter names. Other fold clients,
  richer recursive implementations and some cost proofs still identify source locals.
  Simplification carries array representations across parameter and scalar-result
  binding in the pair's correctness proof. Generated verification conditions
  should handle more of this bookkeeping without hiding genuine data invariants.

## 1. Prove the program that the user writes

Build the proof-facing interface around the existing first-order source language
and compiler. The immediate target is word and array programs with local state,
branches, loops and named recursive calls, not arbitrary Lean compilation.

- Make the source declaration the single executable definition. Expose parameters,
  local variables and returned values to proofs without register arithmetic.
- Build on discarded call results for effectful programming. Scoped standalone
  calls no longer require dummy source bindings, but callees still return words;
  useful typed result signatures, including `Unit`, remain separate work.
- Build on the generated parameter binding, return/time observations and runtime
  entry points. Generate source-facing semantic equations that make larger body
  proofs compositional; keep the input/output driver as an optional executable
  adapter. Producing the entry points alone does not prove an algorithm's contract.
- Extend the scoped traversal rules beyond the expression-update and fixed-helper
  shapes. Sum and count now use the source-derived expression interface, including
  count's additional word parameter. Local helper-result bindings and richer updates
  should reuse the same cursor and framing proofs. Bring richer existing traversal
  and recursive consumers to this source-facing interface, without making clients
  extract expressions or assemble register roles.
- Build on typed local array handles, typed calls and the executable function
  adapter: support structured return values through that same compiled call path.
  Descriptor aliases and borrowed slices now bind locally; general eager array
  expressions, richer typed data and function-returned handles still need work.
  Extend the ordinary application interface to those data operations while
  retaining their effects and safety premises. Do not confuse proof-level `Part`
  observations with executable application, or require a proposed time bound merely
  to express a terminating function.
- Derive verification conditions from that declaration using existing total
  correctness rules. Keep relations and mathematical specifications available;
  a loop need not first become a total pure function.
- Use ordinary Lean induction directly for recursive argument/result contracts.
  Keep body-local specifications only where their stronger information is needed,
  and make richer recursive clients reuse the same parameter and call rules.
- Make the new source-facing interfaces and existing operation clients use
  budget-free program packaging and linking. Attach time certificates later to
  the same code, without requiring a bound to publish functional correctness.
- Keep `Refines`, mathlib equivalences and `StateM` as optional proof interfaces.
  A property such as sortedness is a specification, not a second algorithm that
  the user should have to implement.
- Define result and cost observations through the implementation's actual
  execution. A proposed result function or time bound is something to prove,
  not the definition of what the implementation computes or costs.

**Done when:** an existing array-loop consumer and an existing recursive consumer
each have one executable source definition; their algorithmic correctness proofs
do not use register numbers or stack layouts. Each can be called and verified
without a `main` or stream I/O. They can be linked and used before
choosing time bounds, then receive time proofs without changing the program.

## 2. Compose existing data operations without reopening their implementations

Start with the existing arrays, slices, copy and merge operations. Reuse their
representation, framing and call theorems, together with ordinary Lean and mathlib
objects. Do not add more data-structure wrappers merely to expand a feature list.

- Expose each operation's mathematical effect, safety assumptions and unchanged
  state through a reusable call interface.
- Build on source `include`, generated embeddings and the compiled copy-then-sum
  client to compose richer existing operations without reopening their loops.
  Keep host-level `applyState` sequencing distinct from a single compiled source
  composition, retaining actual linking/call costs, effects and capacity premises.
  Local descriptors and contained slices now compose with an imported operation.
  Returned array values, allocation and richer typed data remain separate work;
  constructing or copying a handle does not implement those data operations.
- Build on the shared expression and verified-call folds for richer existing
  consumers: short-circuiting, multiple accumulators and mutable traversals need
  their actual effects and progress rules. Reuse ordinary `List` folds and their
  algebraic properties, while requiring a proved source implementation of each
  step. Mathematical callbacks are not executable primitives, and their work
  must not be silently free.
- Build on the local borrowed-slice client for mutating subarrays, two live data
  objects and caller data that must survive a call. Keep genuine range, overflow
  and non-aliasing obligations visible. Immutable local handles protect descriptor
  fields, not the heap cells they reference; they do not imply read-only ownership.
- Separate changes of mathematical view from actual data conversion.
  Initialization, copying and conversion must have executable implementations.
- Describe the existing finite-map representation accurately: it is a
  direct-address table over a finite key universe, not a general hash table.

**Done when:** the recursive merge-sort proof composes array and function
specifications without expanding call entry/return or proving frame preservation
cell by cell. A second existing consumer reuses the same rules.

## 3. Turn verified operations into usable cost arguments

The numerical analysis tools are already substantial. The next work is to connect
them to source programs with less mechanical bookkeeping.

- Derive local costs from compiled operations and compose them at actual
  intermediate values. Reuse functional invariants and output-size facts.
- Extend the source-facing separate-time rules beyond assignment prefixes and
  leading/final calls. `ram_time_vc` now advances actual descriptor assignments,
  with compiler-derived costs, before applying an existing callee time bound.
  The copy-then-sum body uses its callee bounds and postconditions without local
  register roles or inner-frame arithmetic. State-dependent remaining bounds are
  available through `FunctionTimeBound.call_seq_at`; the convenience tactic takes
  an explicitly chosen reserve. Richer bodies should expose their mathematical
  cost obligations without reconstructing source statements or frame metadata.
- Expose the implementation's loop sums, recursive-call sizes and nonrecursive
  work without rebuilding the machine simulation in an algorithm proof.
- Extend the constant-cost call fold to data-dependent step bounds using the
  existing finite-sum rules and actual intermediate accumulator/element values.
  A callee contract and a separate cost theorem should compose without a new
  loop induction or manual calling-convention arithmetic in each client.
- Keep the choice of recurrence, invariant or potential as a mathematical
  obligation. Use mathlib to solve the resulting bounds.
- Reuse `Component.Realization` to discharge complete-program obligations:
  fixed legal inputs, encoding, representability, sufficient capacities and
  output observations. Count any implemented loader or representation adapter.

**Done when:** the same loop and recursive consumers admit separate cost proofs
using operation contracts and sums, recurrences or potentials. Their final
certificates describe complete executions on the original legal input domain,
including actual call and entry/exit overhead. Correctness proofs remain
independent of the selected bound.

## 4. Give space bounds their own execution meaning

Prefix resource bounds, maximum composition and partial save/restore facts
already exist. Capacity and the largest accessed address are not live-space
measurements.

First connect the actual nested call history to every execution prefix,
including partially saved and restored frames. Then derive peak stack usage from
those histories and actual frame sizes. General heap-space claims come after
executable allocation, reclamation and reuse have been specified.

**Done when:** a whole-run peak theorem measures live stack slots on the same
machine execution, rather than relabeling a sufficient address-space bound.
A live-heap theorem additionally accounts for allocated and reclaimed storage.

## Later theory work

Cross-model complexity needs an explicit bit encoding, a justified width policy
and a costed simulation of each RAM instruction. Payload bit-size bounds alone
do not supply that simulation. Standard complexity-class claims should follow
those results, not precede them.

Matching lower bounds and tight asymptotics should be added when a concrete
analysis needs them, reusing mathlib's asymptotic relations. An upper recurrence
does not establish a matching lower bound.

## How we work

Advance the first three milestones together through existing consumers.
Prefer a reusable rule that removes repeated proof work over another algorithm
example or a new parallel abstraction. Keep module documentation beside the code,
and keep the [manual](https://vvauted.github.io/Complexity/ComplexityDocs.html)
accurate about which interfaces are ready to use.
