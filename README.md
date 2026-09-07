# Complexity

**Verified programming and complexity proofs in Lean.**

Complexity is a research library for developing executable programs together
with proofs of their functional correctness and resource complexity. Its goal
is to make both kinds of proof resemble ordinary mathematical reasoning in
Lean, while connecting their conclusions to a precisely specified execution
model through verified compilation.

The intended workflow starts from one high-level program. Users reason about
ordinary values and data structures, reuse Lean, Std and mathlib theorems,
and establish resource bounds through compositional rules. Registers, memory
layouts and calling conventions belong in reusable implementation proofs, not
in every algorithm proof. The current word-RAM is an execution backend, not
the intended limit of the programming interface.

[User guide](https://vvauted.github.io/Complexity/Complexity/Doc.html) ·
[API reference](https://vvauted.github.io/Complexity/) ·
[Roadmap](docs/ROADMAP.md)

The guide is maintained in [LeanDoc modules](Complexity/Doc.lean). The website
links above are the configured deployment URLs; hosting requires Pages to be enabled.

## Research direction

- **Separate behavior from cost.** Functional correctness and termination
  should not require a proposed time budget. Complexity analysis can reuse
  functional invariants and is connected to the same implemented computation.
- **Prove at the appropriate abstraction level.** Mathematical specifications
  and resource arguments should compose without repeatedly unfolding machine
  execution. Backend-specific representation and cost assumptions remain
  explicit at the abstraction boundary.
- **Reuse existing mathematics.** Ordinary Lean data and mathlib
  interfaces are the basis for specifications. Representation relations
  connect them to implementations without assuming that every observation
  is a bijection.
- **Justify execution and resources together.** High-level operations need
  verified implementations. Their costs must be derived from execution, not
  assigned by unchecked annotations or arbitrary host-language callbacks.

## Current state

The library currently contains an executable word-RAM semantics, structured
imperative syntax, verified compilation with recursive function calls,
separate total-correctness and time-bound interfaces, and reusable data
representation and framing results. Its complexity layer includes asymptotic
bounds based on mathlib, recurrence and amortized-analysis tools, and
composition of programs and polynomial-time reductions.

Existing array, matrix and finite-map developments exercise these interfaces.
They demonstrate parts of the verified chain; they do not establish that
arbitrary ordinary Lean programs can already be compiled or verified
automatically. A uniform high-level, single-source programming interface and
more backend-independent proof interfaces remain central development goals.

Current time theorems count transitions of the specified word-RAM, including
its fixed-width arithmetic and calling convention. They are not claims about
wall-clock time, bit complexity or a Turing-machine complexity class. Memory
capacity, cumulative address footprint and peak live storage are distinct;
a full treatment of the latter remains unfinished.

## AI-generated content (AIGC)

Substantial portions of the source, proofs and documentation are AI-generated
or AI-assisted. This is an experimental research artifact; no comprehensive
human semantic review is claimed. Lean checks formal proofs against their
stated definitions and assumptions. That check does not establish that a
definition captures the intended problem, that a cost model is appropriate,
or that an informal description accurately states a theorem's scope.

The documentation records the interfaces and model limitations; the
[roadmap](docs/ROADMAP.md) distinguishes established foundations from the
remaining research and implementation work.

## Contributing and license

See [CONTRIBUTING.md](CONTRIBUTING.md). Complexity is released under the
[Apache License 2.0](LICENSE).
