# Contributing

Start with the [roadmap](docs/ROADMAP.md). We are building reusable programming
and proof interfaces; a change should make an existing proof easier or supply a
missing foundation.

## Lean code

Follow mathlib's [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html) conventions.

- Search Lean, Std and mathlib before adding definitions or lemmas.
- Put reusable results under `Complexity/`, by subject. Keep pure mathematics
  independent of RAM, and examples under `Examples/`.
- Use focused imports, small lemmas and the natural declaration namespace.
  Prefer readable proofs over brittle unfolding or large search calls.
- Include a module summary and document public definitions and important results.
  Explain assumptions and meaning, not the history of the implementation.
- Keep functional correctness and termination separate from time bounds.
  Costs must describe the same execution and follow from the compiler.
- Preserve theorem statements when simplifying proofs. No `sorry`, new axioms,
  unchecked cost annotations or hidden changes to overflow and aliasing assumptions.

## Before submitting

Check changed modules and affected consumers with the pinned toolchain, then
build the library. Update `Complexity.lean` when adding a reusable module and
update the [manual](docs/ComplexityDocs.lean) when an interface changes.
[Development instructions](docs/ComplexityDocs/Development.lean) list the build commands.

Keep commits focused. Briefly describe the change and what was checked.
A successful Lean build proves the stated theorem, not that its specification
matches the intended algorithm. Avoid unrelated tooling and generated test scaffolding.

Contributions are under [Apache 2.0](LICENSE). Record substantial AI assistance
in the contribution; the repository's provenance is stated in the README.
