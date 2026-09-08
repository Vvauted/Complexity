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

Function-only declarations and generated word-parameter lists support independent
function contracts. Return values, shared effects and body counts are observations
of the existing execution, with actual call overhead added at call sites. Factorial,
array-copy and array-sum expose this interface. A graph-degree client reuses the
sum contract and mathlib's `SimpleGraph.degree` without register or stack proofs.
The implementations' internal representation proofs still show why the
source-facing work below is unfinished.

`Func.eval` and `Func.bodyTime` expose the same execution through mathlib's `Part`.
The factorial function-value sample states result equations and mathematical
properties without carrying source state in each proposition. These are
noncomputable semantic observations, not yet executable ordinary Lean functions.

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
  loop, register assignments or frame handling. The sum implementation still
  repeats cursor, remaining-length and unchanged-memory arguments. A reusable
  read-only array fold is the next missing data-operation foundation.
- Function-value equations make later mathematical proofs natural, but do not
  make the implementation proof automatic. Semantic `Part` observations and
  executable function application are distinct interfaces.
- Source functions still take words and pointer/length pairs. Typed data views,
  parameter binding and local-state verification conditions need to carry more
  of the routine work before programming feels like ordinary functional Lean.

## 1. Prove the program that the user writes

Build the proof-facing interface around the existing first-order source language
and compiler. The immediate target is word and array programs with local state,
branches, loops and named recursive calls, not arbitrary Lean compilation.

- Make the source declaration the single executable definition. Expose parameters,
  local variables and returned values to proofs without register arithmetic.
- Publish and call intermediate functions without an I/O entry point. Generate
  parameter binding, return observations and semantic equations from the same
  declaration; keep the input/output driver as an optional executable adapter.
- Connect typed executable function application to the existing compiled call
  path. Do not confuse proof-level `Part` observations with a runnable frontend,
  or require a proposed time bound merely to express a terminating function.
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
- Factor array cursor and read-only fold reasoning out of the sum implementation.
  Reuse ordinary `List` folds and their algebraic properties, while requiring a
  proved source implementation of each fold step. Mathematical callbacks are
  not executable primitives, and their work must not be silently free.
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
