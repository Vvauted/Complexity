# Working on Complexity

Read [README.md](README.md), [CONTRIBUTING.md](CONTRIBUTING.md) and
[docs/ROADMAP.md](docs/ROADMAP.md) first. For semantic boundaries and background,
use [docs/DESIGN.md](docs/DESIGN.md) and [docs/LITERATURE.md](docs/LITERATURE.md).
These are the shared project notes; keep useful development guidance in the repository.

## Direction

The goal is one high-level program with reusable correctness and complexity proofs.
RAM is the current backend, not the intended user-facing abstraction.
The next architecture is specified in `docs/HIGH_LEVEL_LANGUAGE.md`: an
independent typed source semantics with source-level proofs and automatically
checked lowering. Algorithm authors must not supply register-level proofs or
per-algorithm lowering adapters. Source-cursor improvements are backend or
compatibility work, not a replacement for that language layer.
Follow the roadmap's priorities and use existing consumers to identify missing
interfaces. Do not substitute more algorithm examples for reusable foundations.

## Code and proofs

- Reuse Lean, Std and mathlib. Keep dependency pins unchanged.
- Follow mathlib naming, focused imports, proof style and module documentation.
  `Complexity/` is the only reusable library root; generic mathematics must not import RAM.
- Preserve theorem meaning and executable semantics. Do not weaken safety,
  overflow, aliasing, uniformity or termination assumptions to close a proof.
- Correctness and termination do not require a proposed time budget.
  Resource bounds must refer to the same computation and justified execution costs.
- No `sorry`, custom axioms, unsafe proof shortcuts or unchecked cost annotations.
- Keep comments about the current interface. Put development history in commits.
  Explain limitations honestly; a checked theorem is not a semantic review.

## Workflow

Develop and commit in the local Complexity checkout. For this session, use the
designated 0v0 checkout for compilation, retaining its pinned dependency cache.
The coordinating agent owns builds; allow at most two concurrent Lean processes.

Use `apply_patch`, preserve unrelated changes, and coordinate file ownership.
Check changed modules and affected consumers before a full build. Use Lean's
existing checks; do not add checksum machinery or unrelated test frameworks.
Commit coherent, verified changes and push regularly when authorized.

The manual is in `docs/ComplexityDocs/`; its entry point is
`docs/ComplexityDocs.lean`. Keep examples and the manual out of the main umbrella.
Do not upload credentials, local environment files or private conversation logs.
