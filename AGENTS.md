# Working on Complexity

Read `README.md` for the project scope and `docs/ROADMAP.md` for priorities.
The goal is one high-level program with correctness and complexity proofs that
compose above the execution model. The current `Ram` library is a verified
backend and a collection of proof interfaces, not the finished frontend.

- Reuse Lean, Std and mathlib before introducing parallel definitions.
- Keep correctness and termination independent of a proposed time budget.
  Resource bounds must describe the same computation and be justified by
  execution. Never replace a cost proof with an unchecked annotation.
- Preserve theorem statements, safety assumptions and executable semantics when
  simplifying proofs. No `sorry`, custom axioms or unsafe proof shortcuts in
  completed results. State incomplete interfaces and model limitations honestly.
- Follow `CONTRIBUTING.md` and mathlib naming and documentation conventions.
  Usage documentation belongs in `Complexity/Doc/`; keep README project-focused.
- Keep reusable results separate from examples. Prefer improving abstraction
  and automation over adding algorithms that repeat low-level bookkeeping.
- Preserve unrelated work and coordinate file ownership with other contributors.
  Use `apply_patch` for edits; do not reset a dirty worktree.
- Use the pinned Lean and mathlib versions. Do not change dependencies
  incidentally or import a second incompatible mathlib.
- For this development session, the user requires compilation on the designated
  build server, not the local workstation. The coordinating agent owns builds;
  allow at most two concurrent Lean processes. Do not add unrelated test
  frameworks, checksum machinery or audit pipelines.
- Check changed modules and affected consumers with Lean. A successful build
  validates the formal statements, not their match to the intended semantics.
- Disclose substantial AI assistance. Do not claim human review that did not
  happen or describe a planned abstraction as an implemented one.
