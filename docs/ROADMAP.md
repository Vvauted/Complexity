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

Function-only declarations generate typed argument lists and `eval`, `bodyTime`
and `run` entry points. The declared word or array parameters come first, followed
by heap capacity and caller state; no input/output `main` is required. Return values,
shared effects and body counts are observations of the existing execution, with
actual call overhead added at call sites. Factorial, array-copy and array-sum
expose this interface. A graph-degree client reuses the
sum contract and mathlib's `SimpleGraph.degree` without register or stack proofs.
Array sum, occurrence counting and the call-based sum of squares share cursor
progress, termination, framing and compiler-derived loop costs. A fold step can
be a read-only source expression or a real call to an already proved function.
The call-based exact-count rule currently requires a constant callee-body count.
Lexical `let`, `let mut` and call-result bindings allocate locals at their
declaration sites. Scoped `for x in xs` binds each loaded element and manages
private cursor locals. For the single-array scalar-call fold, a function rule
infers those locals from generated body and return equations; clients provide
the helper's mathematical contract and array representation premises.
The implementations' internal representation proofs still show why the
source-facing work below is unfinished.

`Func.eval` and `Func.bodyTime` expose the same execution through mathlib's `Part`.
The factorial function-value sample states result equations and mathematical
properties without carrying source state in each proposition. These are
noncomputable semantic observations, not yet executable ordinary Lean functions.
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

Named functions accept array parameters as well as words: `fn sum(xs : array)`
and `call sum(xs)` pass a by-value base address and length through the existing ABI.
`ArrayRef.Rep` connects that reference to an ordinary mathematical list. Sum and
count use this interface; `sumPair` composes two sum calls without reconstructing
their loops or frames. Array-valued locals and returns, allocation and automatic
loading from Lean data remain unfinished.

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
  from a list-sum contract. It assumes a represented adjacency row; it does not
  implement a graph loader or compile a Lean adjacency predicate.
- Reuse can avoid machine-level proofs: the graph client never opens the sum
  loop, register assignments or frame handling. Sum and count now share those
  traversal arguments through `Array.Fold`; count's permutation-invariance proof
  is ordinary `List.Perm.count_eq`. The reusable rules handle one word accumulator
  with a read-only expression or a fixed verified function call, not arbitrary
  Lean callbacks, short-circuiting or mutable traversals.
- Function-value equations make later mathematical proofs natural, but do not
  make the implementation proof automatic. Semantic `Part` observations and
  executable function application are distinct interfaces, now connected for both
  bounded and unbounded runners. State fields for input and output do not imply
  stream operations: the factorial function contract holds at every caller state
  and proves it unchanged. Its `read`/`write` driver is a separate optional program.
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
- The pair's separate cost proof reuses sum's exact count and composes its actual
  call blocks. The unbounded executable application additionally includes the outer
  call and halt. This is a checked path from mathematical list contents to both
  the implementation's returned value and its full call count, not a new loader.
- The source-derived traversal rule currently handles one array parameter, one
  scalar accumulator and a fixed verified two-argument helper. The source syntax
  accepts richer bodies, but their proofs do not yet receive the same convenience.
  Other fold clients and recursive proofs still identify source locals.
  Simplification carries array representations across parameter and scalar-result
  binding in the pair's correctness proof. Generated verification conditions
  should handle more of this bookkeeping without hiding genuine data invariants.

## 1. Prove the program that the user writes

Build the proof-facing interface around the existing first-order source language
and compiler. The immediate target is word and array programs with local state,
branches, loops and named recursive calls, not arbitrary Lean compilation.

- Make the source declaration the single executable definition. Expose parameters,
  local variables and returned values to proofs without register arithmetic.
- Build on the generated parameter binding, return/time observations and runtime
  entry points. Generate source-facing semantic equations that make larger body
  proofs compositional; keep the input/output driver as an optional executable
  adapter. Producing the entry points alone does not prove an algorithm's contract.
- Extend the scoped traversal's source-derived proof rule beyond its first
  single-array scalar-call pattern. Mixed parameters, local helper-result bindings
  and richer updates should reuse the same cursor and framing proofs. Bring
  existing expression-fold and recursive consumers to this source-facing interface,
  without making clients extract expressions or assemble register roles.
- Build on typed array calls and the executable function adapter: support useful
  local data bindings and return values through that same compiled call path.
  Do not confuse proof-level `Part` observations with a runnable frontend, or
  require a proposed time bound merely to express a terminating function.
- Derive verification conditions from that declaration using existing total
  correctness rules. Keep relations and mathematical specifications available;
  a loop need not first become a total pure function.
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
- Build on the shared expression and verified-call folds for richer existing
  consumers: short-circuiting, multiple accumulators and mutable traversals need
  their actual effects and progress rules. Reuse ordinary `List` folds and their
  algebraic properties, while requiring a proved source implementation of each
  step. Mathematical callbacks are not executable primitives, and their work
  must not be silently free.
- Handle subarrays, two live data objects and caller data that must survive a
  call. Keep genuine range, overflow and non-aliasing obligations visible.
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
