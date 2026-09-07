# Contributing to Complexity

Complexity is a research library for verified programming and complexity proofs.
The [roadmap](docs/ROADMAP.md) describes the intended abstraction boundaries;
the [LeanDocs guide](https://vvauted.github.io/Complexity/Complexity/Doc.html)
describes the currently supported interfaces and development commands.

## Mathematical and semantic scope

- Reuse Lean, Std and mathlib definitions and theorems before adding local ones.
- State a mathematical result at the level where it is used. Keep compiler,
  representation and machine arguments reusable instead of repeating them in
  algorithm proofs.
- Separate functional correctness and termination from proposed time bounds.
  Resource theorems may use functional invariants; both must refer to the same
  implemented computation.
- Make overflow, aliasing, input encoding, word width and resource-model
  assumptions explicit. A bound on completed runs is not a termination proof.
- Preserve theorem meaning when simplifying a proof. Do not weaken a statement
  or change an executable merely to make a proof pass.

## Lean style

Follow the [mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
and [style guidelines](https://leanprover-community.github.io/contribute/style.html)
where compatible with the pinned toolchain. Use descriptive module names, small
imports, module documentation, docstrings for public definitions, and ordinary
Lean/mathlib automation. New source files carry the Apache-2.0 license header.

Keep examples separate from reusable interfaces. Documentation belongs in
`Complexity/Doc/` and declaration comments, not in an expanding README tutorial.
The current `Ram` namespace identifies the word-RAM implementation; new generic
infrastructure should not acquire a machine dependency without a reason.

## Checking a change

Check changed modules and their affected consumers with Lean, and run the library
build before submitting. CI builds the library and existing examples;
main-branch builds also generate LeanDocs, with website publication
enabled separately by the repository owner. No separate test framework
is required for a theorem whose statement and proof are checked by Lean.

Do not introduce `sorry`, admitted axioms, unchecked cost annotations or unsafe
proof shortcuts in completed results. Keep the toolchain and dependency pins
unchanged unless the change is explicitly a coordinated version update. A green
build is evidence for the formal statements, not a substitute for reviewing
definitions, assumptions and the intended interpretation.

## AI-generated contributions

Substantial parts of this project are AI-generated or AI-assisted. Disclose
material AI assistance in a contribution's description and explain the intended
semantic change and verification performed. Contributors remain responsible for
the content they submit; neither generation nor successful compilation implies
that a specification is appropriate or has received human semantic review.

Contributions are provided under the [Apache License 2.0](LICENSE).
