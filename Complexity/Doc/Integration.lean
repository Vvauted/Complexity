/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Dependencies and documentation

Complexity reuses existing mathematical and program-semantics infrastructure rather than
maintaining parallel definitions. This chapter covers the pinned dependencies, optional
CSLib package and ordinary development entry points.

## Lean and mathlib

The toolchain is Lean `4.28.0-rc1`; mathlib is pinned to
`5352afccd6866369be9de43f5b7ec47203555f44`.
The machine kernel can use Lean/Std-only imports, while the main proof library directly
depends on mathlib. Smaller topic imports keep dependencies appropriate to a module.

The mathematical layer uses mathlib's actual functions, collections, equivalences, filters,
sums, logarithms and asymptotic relations. Search those APIs before adding a new lemma or
representation wrapper. A bridge belongs here when it connects an existing mathematical
object to the implemented semantics or discharges repeated proof obligations at that boundary.

For native stateful specifications, the library uses `Std.Do.Triple` and `mvcgen` from the
pinned Lean distribution. This does not depend on CSLib or introduce another WP instance.

## Optional CSLib package

`integrations/cslib` is a separate Lake package depending on the local `complexity` package.
It pins CSLib to `232407ba9e7883e71aa57e046f130f52932fc9c8`,
whose Lean and mathlib revisions match the root baseline. It imports official CSLib
definitions instead of copying them. CSLib is Apache-2.0 licensed; retain its upstream
attribution when reusing source.

The integration has its existing `RamCslib` entry point:

```sh
cd integrations/cslib
lake build RamCslib
```

Dependency resolution should retain the checked revisions. Use normal Lake dependency and
cache mechanisms; machine-specific cache paths and local manifests do not belong in the
portable package configuration. Building this integration checks the imported CSLib modules,
not every module in CSLib.

### Execution relations

`RamCslib.Execution` connects `Ram.Exec` to CSLib's `Relation.RelatesInSteps` at exactly the
same step count. Its bounded form connects `TerminatesWithin` to `RelatesWithinSteps` with
a halted endpoint. Faults are not accepted as successful termination.

The runner bridges use the returned step count and state. The bounded successful-run
theorem requires that the runner actually reports halt, not exhaustion or fault.
`RamCslib.Compiler` exports checked callee-sized compilation through the same exact and
bounded relations, retaining output, remaining input and the actual entry/halt steps.

This is a connection to shared execution infrastructure, not a RAM-to-Turing-machine
simulation. It does not establish `SingleTapeTM.PolyTimeComputable` or
`MultiTapeTM.ComputableInTimeAndSpace`.

### Functional models

`RamCslib.Verification` reuses CSLib's labelled-transition and deterministic-automaton
models. `Refines.flts_mtr` composes supplied label implementations into CSLib's existing
extended transition `FLTS.mtr`. That particular statement list is a finite syntax unfolding
for the supplied labels, not a uniform interpreter for unbounded runtime input.

`Refines.finAcc_accepts` transfers the automaton's acceptance predicate through a represented
implementation, covering both acceptance and rejection. It can consume a separately proved
uniform implementation of the extended transition function. Neither bridge assigns one
RAM instruction to one abstract automaton transition: implementation time is proved with the
same `TimeBound` interface as other programs.

The `RamCslib.Asymptotics` and `RamCslib.Polynomial` modules reexport the root library's
mathlib-based interfaces for existing users. They do not maintain another growth theory.

## Building and checking changes

Use a development environment with the pinned toolchain. The ordinary targets are:

```sh
lake build
lake build +Ram.Examples
lake build ram-demo
```

For a focused source check, run `lake env lean path/to/File.lean` from the package root after
its imported dependencies have normal Lake artifacts. A file check is useful feedback; the
library build checks dependency integration. There is no separate generated pass/fail
framework required to establish a theorem.

Completed proofs must be accepted by Lean without `sorry`, custom axioms or unproved cost
annotations. Preserve theorem statements and executable behavior when refactoring proofs.
Compiling a theorem does not determine whether its specification captures the intended
algorithm, size convention or resource claim; those need semantic review.

## Writing and reading LeanDocs

The manual lives in ordinary Markdown module docstrings under `Complexity/Doc`. The
`Complexity.Doc` module imports the chapter modules as a documentation-only entry point;
`Complexity` itself does not depend on the manual. doc-gen4 renders these pages together
with the library API.

The documentation generator is isolated in the `docbuild` Lake package and pinned to
the matching toolchain. Build the HTML manual and API reference with:

```sh
cd docbuild
lake build Complexity:docs Ram:docs
```

The generated site is in `docbuild/.lake/build/doc`. Main-branch CI builds and uploads
the HTML as a workflow artifact. Website publication is opt-in: enable GitHub Pages with
the **GitHub Actions** source, then set the repository Actions variable `PUBLISH_DOCS` to
`true`. The deployment target is [the documentation site](https://vvauted.github.io/Complexity/).
Check the intended website visibility before enabling publication from a private repository.

Keep usage guidance here and declaration-level behavior in the relevant API docstring.
The root README describes the project, its status and AIGC provenance; the roadmap describes
goals and missing capabilities. Development history should not be embedded in API reference
pages as repeated progress reports.

Use descriptive headings, precise declaration references and small source-grounded examples.
Examples involving existing declarations should identify their module and preserve their
actual semantics. Documentation code fences are explanatory text, not a substitute for the
checked source declarations they reference.

The style follows the
[mathlib library conventions](https://leanprover-community.github.io/contribute/style.html):
copyright and license headers, module summaries, conventional names, focused imports and
reusable lemmas. CSLib's organization offers complementary guidance for semantic models and
computer-science interfaces. These conventions guide maintainability; they do not justify
adding redundant abstractions or a large testing framework to a research library.
-/
