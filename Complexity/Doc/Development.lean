/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Dependencies and documentation

Complexity reuses existing mathematical and program-semantics infrastructure rather than
maintaining parallel definitions. This chapter covers the pinned Lean and mathlib dependencies
and ordinary development entry points.

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
pinned Lean distribution, without introducing another WP instance.

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
reusable lemmas. These conventions guide maintainability; they do not justify adding redundant
abstractions or a large testing framework to a research library.
-/
