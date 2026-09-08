/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Development

Complexity uses the Lean toolchain and mathlib revision pinned in the repository.
Start with the [contribution guide](https://github.com/Vvauted/Complexity/blob/main/CONTRIBUTING.md)
and [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md).

## Building

After installing the pinned toolchain and downloading the mathlib cache:

```sh
lake build
lake build Examples ComplexityDocs ram-demo
```

For a focused change, build the affected module by name, for example
`lake build Complexity.Computability.Ram.Array.Traversal`, then check its consumers.
Use `lake env lean path/to/File.lean` for a file check after its imports have been built.

The default target is the reusable library. Examples and the manual are separate consumers.
A successful build checks formal statements; the choice of specification, legal inputs and
cost model still needs mathematical review.

## Finding the right module

```text
Complexity/
  Analysis/Asymptotics/   Growth bounds over ordinary functions
  Analysis/Amortized.lean Potential inequalities over finite histories
  Computability/
    Recurrence/          Numerical recurrence comparison and asymptotics
    Ram/                 Source programs, execution, compilation and program proofs
  Data/                  Supporting Nat and List lemmas
  LinearAlgebra/         Supporting matrix lemmas
  Tactic/Ram/            Proof automation
Examples/                Checked programs and uses of the library
docs/ComplexityDocs/      User manual
docbuild/                Pinned doc-gen4 build package
```

Use the smallest relevant import. Pure mathematics must not import RAM, and reusable modules
must not import the `Complexity` umbrella, examples or the manual.

Module paths locate code; declaration namespaces identify its objects.
For example, `Complexity.Computability.Ram.Basic` defines `Ram.State`, while
`Complexity.LinearAlgebra.Matrix.Update` extends `Matrix`.
The `Ram` namespace is not a separate package.

## Writing documentation

Follow mathlib's [documentation conventions](https://leanprover-community.github.io/contribute/doc.html):
a module comment explains the subject and main results; declaration comments explain meaning
and assumptions. Keep detailed API descriptions beside the definitions and proofs.
The manual explains workflows across modules rather than repeating every theorem.

Use fully qualified declaration names in backticks for API links. Module links use doc-gen4's
`##Module.Name` syntax. Refer readers to checked examples when illustrating a complete proof;
a Markdown code fence is explanatory text, not a checked theorem.

The manual entry point is `docs/ComplexityDocs.lean`. Its modules have a distinct name because
mathlib already owns `docs.*`; they use the same module-comment format and generator.
No separate documentation language or website framework is needed.

## Building and publishing the site

As in the [mathlib documentation build](https://github.com/leanprover-community/mathlib4_docs),
doc-gen4 is a development dependency in its own Lake package. From the repository root:

```sh
cd docbuild
lake build complexity/Complexity:docs complexity/Examples:docs complexity/ComplexityDocs:docs
```

The generated HTML is in `docbuild/.lake/build/doc`. It includes the manual, API search,
module tree, examples and links to the corresponding source.

Main-branch CI builds and publishes that directory through GitHub Pages. The repository's
Pages source is **GitHub Actions**. Pull requests compile the library, examples and manual;
they do not deploy. Generated HTML stays out of the source repository.
-/
