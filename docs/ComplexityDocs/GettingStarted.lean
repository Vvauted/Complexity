/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import ComplexityDocs.GettingStarted.Execution
import ComplexityDocs.GettingStarted.Programs
import ComplexityDocs.GettingStarted.WordRam
import Examples.Language.Factorial
import Examples.Language.FactorialCompiled
import Examples.Language.OptionalBuffer
import Examples.Language.OptionalBufferCompiled
import Examples.Language.Scalar
import Examples.Language.ScalarCompiled
import Examples.Language.ScopeCompiled
import Examples.Language.Traversal

/-!
# Getting started

Write one high-level source program and state its correctness with ordinary Lean
values and mathlib. Verified lowering connects that implementation to word-RAM
execution and separately proved resource bounds. The direct word-RAM language
remains available for backend work and explicitly low-level implementations.

## Install and build

Install Lean through [elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/Vvauted/Complexity.git
cd Complexity
lake exe cache get
lake build
```

The repository pins Lean `4.28.0-rc1` and a matching mathlib revision.
The cache command downloads mathlib artifacts; the build checks Complexity itself.

To use the library from another Lake project with the same toolchain, add:

```toml
[[require]]
name = "complexity"
git = "https://github.com/Vvauted/Complexity.git"
rev = "<commit-or-release>"
```

Choose a commit or release, then import `Complexity` or a focused module:

```lean
import Complexity.Computability.Ram.Verification.Refinement
import Complexity.Computability.Recurrence.Basic
```

The first import is for program proofs; the second provides numerical recurrence lemmas
without a RAM dependency. Examples are separate and build with `lake build Examples`.

## Write a high-level function

The [typed frontend](##Complexity.Language.Syntax) has one recommended entry,
`source_program P where`, for ordinary parameters, local variables, calls and
recursion. `P.f` names the actual source action; when a checked total mathematical
view can be generated, it is named `P.f_model`. A missing total model does not
by itself reject the source program. The default entry is connected; complete
control-flow integration remains in progress.

For example, the [scalar program](##Examples.Language.Scalar) calls a helper
and updates a local value:

```lean
import Complexity.Language.Syntax

source_program Implementation where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if limit ≥ next then
      result := next
    return result
```

Its mathematical correctness statement is
`Implementation.boundedIncrement_model n limit = min (n + 1) limit`.
The generated correspondence transfers this equation to the same source
implementation. Its `boundedIncrement_total` contract additionally records that
the actual heap is unchanged; the user does not prove the branch's heap plumbing.
Correctness requires no proposed time budget or word width.

Some existing examples retain compatibility names. `(pure)` exports the
mathematical function under `P.f` through the older scalar interface;
`(native)` retains its earlier naming layout for represented values. These are
not modes to select for each new language feature. The existing recursive
factorial uses the `(pure)` compatibility API:

```lean
import Complexity.Language.Syntax

source_program (pure) Implementation where
  def factorial (n : Nat) : Nat := do
    if n == 0 then
      return 1
    else
      let previous ← factorial (n - 1)
      return n * previous
    termination_by n
    decreasing_by simp_wf; simp_all +zetaDelta; omega
```

The correctness statement is simply
`Implementation.factorial n = Nat.factorial n`. The
[complete proof](##Examples.Language.Factorial) uses ordinary induction and
mathlib's factorial equation. Generated correspondence transfers that result to
the source program without a second implementation or recursion proof.
No time budget or word width appears in this mathematical theorem.

Finite-range loops can also generate an ordinary total function. This existing
example retains the same compatibility API:

```lean
source_program (pure) Iterative where
  def factorial (n : Nat) : Nat := do
    let mut acc := 1
    for i in [:n] do
      acc := acc * (i + 1)
    return acc
```

The same example proves `Iterative.factorial n = Nat.factorial n` with ordinary
fold and product identities. Generated correspondence supplies the total source
contract without a second loop-termination proof.

Ordinary structures can also be registered with `source_type`. The
[scalar example](##Examples.Language.Scalar) registers a `BoundedInput` with
`value : Nat` and `limit : Nat`, then constructs, passes, returns and projects it
in one default `source_program` declaration. Its correctness theorem
is the ordinary equation `Structured.run_model n limit = min (n + 1) limit`.
Its caller groups construction, the helper call and projection in an ordinary
`let result : Nat ← do ...` block, then returns that result. The same local-return
boundary handles this form and conditional/Option value branches.
The generated `Structured.run_refines.of_math` transfers that mathematical proof
to the same source implementation; the
[compiled client](##Examples.Language.ScalarCompiled) proves its actual RAM
result and independent instruction bound using shared range and cost rules.
The checked raw-input reconstruction for its automatic total contract supports
closed structures with direct scalar or scalar-product fields, not arbitrary
Lean datatypes or dependent fields. This is a proof-generation boundary, not
a restriction excluding array-valued source records.
The same scalar file retains a compatibility example with such a structure as a finite-range accumulator,
calling a structure-valued helper in each round with a dynamic positive stride.
`StructuredRange.sum` has an ordinary fold/sum proof and generated total source
contract. Its complete function-body instruction bound reuses generated native
guard/body equations and the shared range cost rule, without hand-written
capture indices or a second round-count proof. The compiled client also proves
finite-word realization and a halted RAM invocation, retaining explicit bounds
on the computed sum, cursor, stride and launch capacity. General loops with
represented records use the state-contract interface described below.

Products and options are ordinary values too. The
[structured client](##Examples.Language.OptionalBuffer) imports a helper returning
`Option (Nat × Nat)`, then returns a length and optional borrowed buffer to its
caller. Ordinary bindings such as `let (length, present) ← Library.inspect xs`
and patterns such as `some (length, offset)` destructure that same actual result;
the right-hand side is evaluated once. That caller modifies the first cell only when
present. Its specification uses an ordinary `Array.modify` result and preservation
of outside views, not register identities. Effectful programs use mathematical
contracts rather than pretending that borrowed mutation is a pure operation.

The [high-level proof guide](ComplexityDocs/Verification.html) explains the two proof
views: ordinary function equations when a total model is available, and
mathematical state contracts for the actual source execution. The source language
includes `while`, bounded `for`, borrowed buffers, allocation and scoped scratch
reclamation. Automatic total models cover supported combinations, not every
loop or recursive family; general `while` uses explicit state contracts.
The remaining control-flow integration does not make an optional model a
precondition for accepting source code. This is a checked executable subset,
not a compiler for arbitrary Lean definitions.

The [mutable traversal](##Examples.Language.Traversal) writes its actual loop as:

```lean
for i in [:xs.length] do
  let x ← xs.get i
  let y ← increment x
  if y ≤ limit then
    xs.set i y
  else
    xs.set i limit
```

The mathematical specification is still an ordinary `Array.map`. The author
supplies a processed-prefix invariant; generated loop contracts retain the
actual heap and distinguish normal completion from function return. Buffer
iteration reads current cells, not an entry-time snapshot. General aliasing is
not disabled to simplify the proof.

## Connect the same function to RAM

Native Lean evaluation is not the certified cost model. For RAM execution, prove
the source program's actual values fit the selected word width and give sufficient
storage, separately from correctness. An independent instruction bound uses the
compiler's operation and call costs. The
[compiled factorial](##Examples.Language.FactorialCompiled) and
[structured client](##Examples.Language.OptionalBufferCompiled) use the shared
`FunctionRealizable.execute_le` rule to obtain a typed actual runner result with
the mathematical postcondition and step bound; authors do not reconstruct a
register-level simulation or a large runner tuple.

Uniform structural budgets can be inferred from the existing compiler cost
rules. The compiled traversal derives its guard, body and wrapper bounds once;
direct, composed and imported clients reuse those names. This removes copied
numeric charges, not the mathematical loop invariant, range conditions or
potential argument. The iterative native factorial above does not acquire a RAM
cost bound merely from its equality proof.

For a pure finite range, the shared
[range cost rule](##Complexity.Computability.Ram.Compiler.Language.CostBound.Range)
uses the same native guard/body equations as the correctness bridge. It combines
proved component budgets with `Std.Legacy.Range.size`, including positive
dynamic steps and early returns. The structure-valued range consumer above
uses this rule; it does not duplicate a loop evaluator, block-contract adapter
or division-count descent argument. `structuredRangeSumBodyBound_eq` exposes
the inferred bound as a constant times the ordinary range length plus a fixed
overhead, so subsequent numerical reasoning need not unfold the compiler.

Allocating programs use the corresponding
[arena result](##Complexity.Computability.Ram.Compiler.Language.Arena.FunctionExecution),
which retains actual final memory, the allocation cursor and known call depth.
The [scratch client](##Examples.Language.ScopeCompiled) adds its mathematical
array contents and a physical workspace bound independent of repetition count.
These invocation guarantees assume preloaded inputs; host loading and conversion
are not silently included in the instruction count.

The [shared allocating map](##Complexity.Language.Buffer.Map.Program) can reuse
an existing scalar source function, including its internal calls. Its
[RAM connection](##Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Execution)
retains `Array.map` output in fresh storage and all old contents observations.
The bound counts output initialization, every real callback and the outer
invocation. A uniform callback bound gives `linearInvocationBound`, a bound
depending only on input length with compiler-derived overhead. The shared
[asymptotic theorem](##Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Asymptotics)
gives mathlib `IsBigO` for this same budget without unfolding those coefficients;
the execution still requires the stated input ranges and available storage. Existing scalar
range and cost proofs are reusable through the
[callback bridge](##Complexity.Computability.Ram.Compiler.Language.Buffer.Map.Scalar).
This is currently a typed-core library operation, not native `xs.map f` syntax
or support for arbitrary Lean callbacks.

## Continue by task

- [State a correctness-and-complexity task](ComplexityDocs/GettingStarted/Programs.html):
  fixed mathematical inputs and outputs, `Program.Correct` and `Program.TimeO`.
- [Prove source correctness](ComplexityDocs/Verification.html): mathematical equations,
  mutable contracts, loops, calls and their checked connection to RAM.
- [Write direct word-RAM code](ComplexityDocs/GettingStarted/WordRam.html): the separately
  supported low-level language, borrowed arrays and example proofs.
- [Execute direct word-RAM functions](ComplexityDocs/GettingStarted/Execution.html):
  runners, executable values and optional stream drivers.

Return to the [manual index](ComplexityDocs.html) for data models, complexity analysis
and backend assumptions.
-/
