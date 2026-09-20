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
- Split modules at semantic or proof responsibilities, not arbitrary line counts.
  Keep mutually recursive passes and a single induction together when splitting
  would obscure their invariants. See the [module guide](docs/STRUCTURE.md).
- An aggregate import may preserve a stable entry point; implementation modules
  import their dependencies directly, never their own aggregate. Keep internal
  elaborator helpers in the implementation namespace and local helpers private.
  Moving declarations must preserve generated names, registration order and
  executable bodies, not merely make existing imports compile.
- Keep functional correctness and termination separate from time bounds.
  Costs must describe the same execution and follow from the compiler.
- Preserve theorem statements when simplifying proofs. No `sorry`, new axioms,
  unchecked cost annotations or hidden changes to overflow and aliasing assumptions.

## Before submitting

Check changed modules and affected consumers with the pinned toolchain, then
build the library. Update `Complexity.lean` when adding a reusable module and
update the [manual](https://vvauted.github.io/Complexity/ComplexityDocs.html) when an interface changes.
[Development instructions](https://vvauted.github.io/Complexity/ComplexityDocs/Development.html)
list the build commands.

Keep commits focused. Briefly describe the change and what was checked.
A successful Lean build proves the stated theorem, not that its specification
matches the intended algorithm. Avoid unrelated tooling and generated test scaffolding.

Contributions are under [Apache 2.0](LICENSE). Record substantial AI assistance
in the contribution; the repository's provenance is stated in the README.
