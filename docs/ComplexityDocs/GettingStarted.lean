/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Getting started

This page takes you from a checkout to a running program and a complete checked proof.
The current language is a structured word-RAM language; specifications can use ordinary
Lean functions, relations and mathlib.

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

## Define a function

The source syntax supports local variables, expressions, memory operations, I/O,
conditionals, loops, named functions and recursive calls:

```lean
import Complexity.Computability.Ram.Source.Named.Declaration

open Ram Ram.DSL

ram_def functions := ram_functions% {
  fn factorial(n) locals (answer) {
    if n {
      answer := call factorial(n - 1);
      answer := n * answer;
    } else {
      answer := 1;
    }
    return answer;
  }
}
```

Names resolve to source registers and function-table entries, including forward and mutual
recursive calls. Runtime values are words: multiplication wraps unless range hypotheses
justify its interpretation as natural-number multiplication.
Return expressions occur at the end of functions; early return, `break` and `continue`
are not current constructs.

This is the function declaration from [the factorial example](##Examples.Ram.Factorial).
No `main`, input stream or output stream is required. `functions.function.factorial`
is the actual function; `functions.arguments.factorial` constructs its argument list
from typed word parameters. Both are generated from this one declaration.
The [declaration interface](##Complexity.Computability.Ram.Source.Named.Declaration)
also exports lookup facts and source-local names for implementation proofs.
These names do not yet hide every register-level obligation inside those proofs.

## Add an executable driver when needed

`Ram.Named.Functions.withMain` supplies an explicit entry statement without changing
the functions. A driver may read inputs and write results; ordinary function calls
and their correctness proofs do not require it. `ram_program%` remains available
when a complete program is the natural starting point.

`Ram.Named.Bundle.executable` checks and prepares a named program, returning an
`Option Ram.Executable`. `Ram.Executable.run` takes a transition limit and input words.
Its result distinguishes normal halt, fault, invalid program counter and exhausted fuel.

The compiled entry first reads a heap-boundary header; remaining input words are read by
the source program. Preparing or loading a data structure is not implicitly supplied by a
mathematical representation. See [the backend](##ComplexityDocs.Backend) for these boundaries.

For a ready-to-run demonstration, use the existing array-fill-and-sum driver:

```sh
lake exe ram-demo fast 1000
lake exe ram-demo reference 1000
```

Here `1000` is the array length; the driver computes the execution limit internally.
Both runners execute the same code and input. Their measured host runtimes are distinct
from the formal RAM transition count.

## Follow a complete proof

Start with [the factorial example](##Examples.Ram.Factorial).
Its function is defined independently of the optional stream adapter.
Read its declarations in this order:

1. `Ram.Examples.Factorial.function_contract` states the returned value and unchanged caller state.
2. `Ram.Examples.Factorial.function_runs` gives a safe invocation with an explicit argument.
3. `Ram.Examples.Factorial.function_result` identifies the returned natural number with
   mathlib's factorial when the result fits in a word.
4. `Ram.Examples.Factorial.function_timeBound` separately bounds the same body's execution.
5. `Ram.Examples.Factorial.runs` includes the optional stream adapter and all machine overhead.

The general result is factorial modulo the word range, not unbounded arithmetic.
The source-level recursive proof still needs local representation facts; the public
function contract does not expose those registers to its callers.
For optional native `StateM` verification, see [the increment example](##Examples.Ram.Verification).
Continue with [proving correctness](##ComplexityDocs.Verification).

## Choose a larger example

| What you want to study | Checked example |
| --- | --- |
| Linking independently verified programs | [Composition](##Examples.Ram.Composition) |
| Array traversal and an ordinary list model | [Array sum](##Examples.Ram.ArraySum) |
| Recursive mathematical specifications | [Factorial](##Examples.Ram.Factorial) |
| A logarithmic time bound | [Bit length](##Examples.Ram.BitLength) |
| Potential-based amortized analysis | [Amortized clearing](##Examples.Ram.AmortizedClear) |
| Reusing an array contract and its frame | [Array copy](##Examples.Ram.ArrayCopy) |
| Lower bound with duplicates | [Binary search](##Examples.Ram.BinarySearch) |
| Recursive calls, borrowed arrays and a recurrence | [Merge sort](##Examples.Ram.MergeSort) |

These examples illustrate the current interfaces, including places that still require
representation and register-level proofs. The [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md)
focuses on removing that repeated work without changing the executable meaning.
-/
