# Roadmap

## Objective

Complexity aims to support ordinary programming in Lean with machine-checked
proofs of both functional correctness and resource complexity. Users should
write one high-level program and reason primarily about its mathematical
behavior, data structures and resource requirements. Verified compilation
and representation theorems must connect those proofs to actual execution.

The objective is not simply a convenient notation for RAM instructions, an
analyzer for user-assigned ticks, or a collection of separately verified
algorithms. The word-RAM is the first backend. Both functional and complexity
proofs should become substantially independent of its registers, instruction
sequences and stack layout, without hiding model-dependent assumptions.

This roadmap distinguishes existing foundations from the interfaces still
needed to achieve that experience. A checked low-level theorem or a working
example does not by itself complete a high-level programming milestone.

## Established foundation and present limits

The repository already provides a fixed word-RAM semantics and executable
runner, structured expressions and statements, named first-order functions
and recursion, checked compilation, and execution-preservation theorems with
compiler-derived transition counts. Calls, independent module linking and
complete halted executions are part of this foundation.

Safe total-correctness contracts are separate from time bounds. Representation
relations connect implementations to ordinary Lean values, and existing
stateful bridges reuse native `StateM`, `Std.Do.Triple` and `mvcgen`. Array,
matrix and finite-map developments show that mathematical properties can be
proved separately from memory and call bookkeeping. These bridges are not
yet a compiler from arbitrary Lean or `StateM` programs.

The complexity layer reuses mathlib's asymptotics, filters, sums and logarithms.
It includes recurrence comparison, amortized reasoning, uniform and
multivariate bounds, resource-aware composition and polynomial-time
reductions. CSLib integration uses upstream execution relations and selected
automata models; it does not prove equivalence to a Turing-machine cost model.

Actual execution prefixes, address footprints and sufficient stack capacity
are formalized. They are not interchangeable with peak live space. Tight
stack histories, allocation-aware space semantics and bit-cost simulation
remain incomplete.

## 1. A single-source high-level programming interface

**Highest priority.** Complete a compositional front end for local variables,
structured control flow, functions and recursion, and typed data operations.
Its surface should support ordinary program construction without requiring
users to assign registers, choose stack slots or duplicate a program as a
handwritten reference implementation.

- Give supported constructs a clear high-level semantics and reusable
  lowering rules with preservation proofs. Existing source syntax and
  compiler results should be reused rather than replaced without need.
- Make parameter passing, return values, local state and data access compose
  through the same interface, including inside loops and recursive calls.
- Derive the semantic view needed by verification from the program. Pure
  functions and native `StateM` are useful semantic interfaces, not mandatory
  second programs that users must author and relate to RAM by hand.
- Keep the supported executable fragment explicit. Mathematical definitions
  used in specifications are not automatically executable primitives;
  unbounded work cannot enter the language as a constant-cost Lean callback.

**Completion evidence:** existing nontrivial programs can be expressed once,
proved through their high-level interfaces, and compiled to the actual
backend. Their algorithm proofs do not reconstruct registers, call frames or
a second implementation. This requires the whole path, not just expression
compilation or attractive syntax.

## 2. Reusable data structures and representation proofs

Build a standard library in which an operation exposes its mathematical
meaning, safety requirements and justified resource behavior together.
Representation proofs belong to implementations and should be reusable
across algorithms and combinations of data structures.

- Use ordinary Lean/mathlib objects wherever possible: sequences and arrays,
  records and products, finite functions, matrices, sets and partial maps.
  Reuse CSLib structures where they supply the relevant semantic interface.
- Make lookup, update, traversal, subviews and function boundaries compose
  without repeated pointwise heap proofs. Preserve unrelated state and
  account honestly for aliasing and scratch space.
- Use relations, equivalences or quotient observations according to what
  the representation actually preserves. Forgetting order or multiplicity
  must not turn an implementation into a stronger specification.
- Treat conversions, initialization, allocation and resizing as implemented
  operations when they perform runtime work. A proof-only change of view
  and a data conversion must not acquire the same resource specification.

**Completion evidence:** existing operations compose over multiple ordinary
data models without new per-use adapters. Adding a representation requires
its operation laws once; clients reuse those laws and upstream mathematics.
The target is not a growing inventory of thin type-specific wrappers.

## 3. Verification at the program level

Functional correctness should concern returned values and changes to abstract
data. Termination may require a variant or well-founded relation, but must
not require selecting an instruction-count budget first.

- Generate verification conditions from supported high-level programs,
  reusing Lean's native verification infrastructure where applicable.
- Normalize represented observations and apply operation/function contracts
  without exposing backend states. Keep loop invariants and recursive
  hypotheses in ordinary mathematical form.
- Package reusable safety and framing arguments at library and compiler
  boundaries. Preserve genuine bounds, overflow and non-aliasing obligations
  rather than treating them as automatically true.
- Automate routine substitution, state updates, frame transport and justified
  arithmetic. Fail with the remaining mathematical obligation visible; do
  not hide failure behind unproved annotations or a second trusted verifier.

**Completion evidence:** refactoring an implementation's register layout does
not require rewriting its high-level correctness proof. Existing consumers
use mathematical specifications and ordinary Lean tactics; custom automation
removes mechanical work without guessing an invariant or changing a goal.

## 4. Compositional complexity proofs above the machine

Complexity analysis needs the same abstraction discipline as correctness.
Users should prove bounds over input sizes, traversals, recurrences and
potentials, using verified operation costs rather than expanding compiled
instruction lists at every step.

- Expose resource contracts for high-level operations and preserve them
  through compilation with a proved relation to target execution.
- Compose sequential, branching, looping and recursive bounds at the actual
  intermediate values. Reuse functional invariants and output-size facts
  without making functional correctness depend on a proposed cost bound.
- Improve the existing finite-sum, logarithmic, recurrence and amortized
  interfaces around real proof friction. Retain initial/final potential and
  generated work, including repeated occurrences in dynamic worklists.
- Automate routine bound normalization and application of established
  recurrence/asymptotic results. The programmer still supplies the essential
  recurrence, potential or mathematical argument when it is not derivable.

**Completion evidence:** an algorithm's resource proof is expressed in
abstract operation contracts and standard mathematical bounds. Backend
instantiation supplies justified costs, representation assumptions and
overhead theorems. This is independence from machine bookkeeping, not a claim
that every machine model gives the same complexity.

## 5. Complexity-theoretic and resource foundations

Maintain foundational work alongside the programming interface. Higher-level
proofs need a sound way to state which problem, size measure and computational
resource their conclusions concern.

- Extend reusable size and encoding interfaces, including costs of genuine
  representation changes. Preserve uniform programs, admissible inputs and
  word-width assumptions through composition and reductions.
- Reuse mathlib asymptotic relations and filters directly. Distinguish
  concrete bounds, asymptotic upper bounds and tighter claims; an upper-bound
  recurrence alone does not establish a matching lower bound.
- Complete actual nested-call histories for tighter peak-stack results,
  accounting for partially saved and restored frames. Distinguish capacity,
  cumulative footprint and live storage throughout the public interface.
- Specify allocation and reclamation before claiming general live-heap
  bounds. Extend resource composition only with a corresponding execution
  interpretation, not by relabeling an existing address bound as space.
- Develop explicit bit-level encodings and a costed simulation for comparison
  with other computation models, reusing CSLib machinery where suitable.
  Complexity-class claims require those simulations and their hypotheses.

**Completion evidence:** resource and model-change theorems identify the same
implemented computation and state their encoding, simulation and uniformity
conditions. New backends reuse high-level proof interfaces through verified
connections; they do not inherit RAM theorems by terminology alone.

## 6. Library organization and documentation

Follow mathlib/CSLib conventions where they fit this research library:
descriptive module and declaration names, small imports, documented public
definitions, reusable lemmas before applications, and explicit dependency
boundaries. Prefer upstream concepts to parallel local foundations.

The README explains the project, research scope and AI-generated content.
The [Lean documentation](https://vvauted.github.io/Complexity/Complexity/Doc.html)
contains the user guide; the [API reference](https://vvauted.github.io/Complexity/)
documents public interfaces. Both should state supported programming
constructs, proof interfaces and model limitations. Architectural notes should
explain decisions rather than grow into chronological lists of declarations.

Keep builds reproducible under pinned dependencies and check changed Lean
modules with the compiler. Avoid unrelated test frameworks, bookkeeping
machinery or a proof-count scoreboard. AIGC disclosure and semantic review
remain necessary: successful type checking proves formal statements, not
their fidelity to an intended algorithm or cost interpretation.

## Work order and criterion for progress

Use existing algorithm developments to drive priorities 1–4 together: expose
an actual programming or proof obstacle, improve the reusable interface, and
carry the same program through correctness, complexity and execution again.
Do not substitute more benchmark solutions for the missing abstractions.

Advance priority 5 where it supports that work, while keeping incomplete
space and cross-model results visible. Maintain priority 6 continuously.
Progress means that ordinary programs require fewer implementation-specific
proofs while retaining their verified execution and resource guarantees.
The goal is not complete until that experience works across program
composition and data structures, for both correctness and complexity.
