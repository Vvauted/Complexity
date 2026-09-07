# Execution and refinement design

The project-level goal and development priorities are in [ROADMAP.md](ROADMAP.md).
Users should write one high-level program and reason about ordinary mathematical
objects and compositional resource bounds. Both kinds of proof should hide
reusable representation and machine details. The word-RAM described here is the
current backend, not a requirement that users manually write a second program
or prove every algorithm directly over registers. `StateM` is an optional model
interface; it is not a mandatory second source language.

## Scope and completion obligations

The backend-facing layer supports an executable, structured first-order language with
functions, recursive calls, local variables, arrays and control flow. We must
prove the program layer agrees with the specified RAM machine, not merely build
an interpreter or verify a manually instrumented cost function.

Required layers:

1. A fixed word-RAM instruction set and deterministic executable transition.
2. A single transition-counting relation, compositional execution lemmas, and
   an executable bounded runner agreeing with that relation.
3. Structured expressions/statements and first-order function declarations,
   with a clear source semantics (including effects and termination).
4. Compilation to the machine, with result/memory/control preservation and
   a machine-step theorem for every supported construct, including calls.
5. Derived proof rules and useful arithmetic, array and function-frame lemmas.
6. Source syntax and examples that use the same program for execution and proof.

These are backend obligations. Meeting them is necessary but does not by itself
provide the general single-source frontend or high-level proof automation in the
roadmap. An expression compiler, straight-line code, or an annotated while
language alone is also insufficient.

## Cost model

We adopt a word-RAM, not an unlimited-integer unit-cost RAM. A word is a
`BitVec w`; arithmetic, addressing and comparison have explicit bit-vector
semantics. The finite instruction vocabulary includes word multiplication.
This is a public machine-model choice, not a claim that multiplication was
derived in constant time from addition. Exact mathematical multiplication is
recovered under a proved no-overflow condition; without it the result is modular.

The only unit-time rule is one executed machine transition. No constructor of
the source language accepts a cost. Source expressions and statements lower to
finite target code, and their costs follow from executions of that code. Source
function calls may not copy an unbounded frame or argument list for one step;
such work must be represented by actual target instructions.

Machine time is not the wall-clock time of the Lean interpreter. Any optimized
execution representation needs a correspondence theorem before replacing the
reference interpreter in the claimed verified chain.

## Semantics boundaries

- Source operators are fixed constructors, not arbitrary `Lean` callbacks.
- Proofs, specifications, invariants and potentials cannot affect runtime data.
- A cost certificate includes termination; a conditional statement about an
  execution that may not exist is insufficient.
- A whole program and its compilation layout are fixed before input size and
  word width are quantified. Constants cannot conceal input-dependent layouts.
- The benchmark, not the submitter, fixes legal inputs and admissible word widths.
- Input encoding and preparation costs are explicit per benchmark contract.
  Text decoding may be external; algorithmic preprocessing is not implicitly free.
- Assertions describe mathematical relations on outputs, not necessarily equality
  to a designated reference implementation.

## Library/version policy

Keep the base Lean/Std dependency small and pinned. The matching mathlib revision
is `5352afccd6866369be9de43f5b7ec47203555f44`; imports can be added when needed.
Neither a moving upstream branch nor a reference project's advertised theorem
is a substitute for checking this repository's corresponding theorem. The
asymptotic layer uses mathlib's `IsBigO` directly. RAM-to-Turing-machine simulation
and membership in a Turing-machine complexity class require additional proofs.
