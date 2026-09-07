/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Getting started

This chapter introduces the current structured source language and library entry points.
Read [functional verification](##Complexity.Doc.Verification) next for the proof workflow.

## Installation

Install Lean through elan, then use the repository's pinned `lean-toolchain`. A checkout
builds with:

```sh
git clone https://github.com/Vvauted/Complexity.git
cd Complexity
lake exe cache get
lake build
```

The cache command downloads available mathlib artifacts; the library itself is checked by
the build. The toolchain is Lean `4.28.0-rc1`. Dependency revisions are pinned in the Lake
configuration rather than selected from moving upstream branches.

For a downstream Lake project using that toolchain, add a dependency on this repository.
Select a commit or release for reproducible work:

```toml
[[require]]
name = "complexity"
git = "https://github.com/Vvauted/Complexity.git"
rev = "<commit-or-release>"
```

Then use:

```lean
import Complexity
```

The backend declarations retain their `Ram` namespaces and import paths. Topic imports such
as `Ram.Verification.Refinement`, `Ram.Matrix.Memory` or `Ram.Complexity.Recurrence` avoid
loading the entire library. Examples have the separate entry point `Ram.Examples`.

## Programs and named variables

The frontend in `Ram.Syntax` resolves named locals to registers. The source vocabulary
includes expressions, array-addressed reads and writes, assignment, input and output,
conditionals, loops, first-order calls and recursion.

This small multiplication function illustrates the existing syntax:

```lean
import Ram.Syntax

open Ram Ram.DSL

def multiply : Func := ram_fun% (a, b) locals (answer) {
  answer := a * b;
  return answer;
}
```

To link declarations and an entry block, use `ram_program%`:

```lean
import Ram.RunProgram

open Ram Ram.DSL

def exampleProgram : Named.Bundle := ram_program% {
  fn multiply(a, b) locals (answer) {
    answer := a * b;
    return answer;
  }
  main locals (a, b, answer) {
    read a;
    read b;
    answer := call multiply(a, b);
    write answer;
  }
}
```

These are source-language examples, not claims that multiplication on unbounded naturals
takes one step. Runtime values are machine words, with modular arithmetic unless range
hypotheses justify their natural-number interpretation.

`ram_program%` resolves forward calls and mutual recursion. Function names and local
variables have separate scopes; embedded `const(t)` expressions retain the enclosing Lean
scope. A return expression appears at the end of a function. Early return, `break` and
`continue` are not currently language constructs.

With `import Ram.Named.Declaration` (or `import Complexity`), use the declaration form
`ram_def p := ram_program% { ... }` when proofs need source names.
It also exports ordinary Lean abbreviations such as `p.mainReg.x`, `p.localReg.f.x` and
`p.functionIndex.f`, using the same resolver as compilation. There is no runtime name lookup.

This named source language is useful today, but it is not yet the planned general frontend
with automatic data representation and high-level proof generation. In particular, a Lean
function used in a specification is not silently treated as an executable primitive.

## Preparing and executing a program

`Ram.Named.Bundle.executable` checks and prepares a named program, returning an
`Option Ram.Executable`. Preparation stores the compiled instructions in an array and can
be reused for multiple inputs. `Ram.Executable.run` accepts a transition limit and a list of
input words; its result records the actual steps, final state and stopping reason.

The stopping reasons distinguish normal halt, fault, invalid program counter and exhausted
fuel. A stopped or faulting run is not a successful correctness certificate. The runner's
fuel is an execution limit, not a parameter required by a functional specification.

For programs produced by this compiler, the first input word supplies the source-heap/stack
boundary; the remaining words are read by the user program. A preloaded-block theorem may
instead start at an explicitly represented memory state. Such a theorem does not include an
unimplemented input loader or output serializer.

`Ram.Executable.run_eq` relates the entire decoded result of the fast backend to the reference
runner. This includes the final observations, transition count and stopping reason.
`Ram.runExact` remains an exact-step mathematical interface; it is not the usual bounded runner.

## Existing examples

The examples are source files with checked definitions and theorems, not a separate testing
framework. They illustrate different proof boundaries:

| Example module | What to read it for |
| --- | --- |
| `Ram.Examples.Verification` | I/O refinement, native `StateM` and separate time analysis |
| `Ram.Examples.Composition` | Linking independent modules through a shared representation |
| `Ram.Examples.ArraySum` | A native traversal model connected to a fixed array loop |
| `Ram.Examples.Factorial` | Mathematical recursive specification using `Nat.factorial` |
| `Ram.Examples.BitLength` | A well-founded numerical model and a separate logarithmic time bound |
| `Ram.Examples.AmortizedClear` | Potential-based analysis of actual push and clear operations |
| `Ram.Examples.ArrayCopy` | Reusing a preloaded-array contract and exporting its memory frame |
| `Ram.Examples.BinarySearch` | Lower bound, duplicates and ordinary `List.findIdx` specifications |
| `Ram.Examples.MergeSort` | Recursion, borrowed arrays, scratch and a balanced recurrence |
| `Ram.Matrix.MergeSort` | Reusing the sorting implementation through a native matrix-row model |

`Ram.Examples.Arithmetic` distinguishes modular and no-overflow multiplication. Array fill,
triangular loops, insertion sort, linear merge and unequal call frames supply further
consumers of the same library interfaces.

Compile the examples separately with `lake build +Ram.Examples`. To run the existing native
demonstration:

```sh
lake exe ram-demo fast 1000
lake exe ram-demo reference 1000
```

Here `1000` is the array length; the driver computes its execution limit internally.
The driver executes one named program that writes an array and then sums it. Both backends
use identical code, input and transition limits. Host timings depend on the interpreter and
environment; they are distinct from the formal RAM transition count.
-/
