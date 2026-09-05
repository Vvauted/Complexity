# ram-lean

A Lean 4 library for structured imperative programs whose functional correctness,
termination, and running time are tied to a fixed word-RAM execution semantics.

The structured language, compiler, and initial proof library are implemented
and checked against the target machine, including ordinary recursive calls.
This is a research library with explicit word-size and memory-safety premises;
see the verification evidence and boundaries in [progress](docs/PROGRESS.md).

## Intended contract

A submission is one finite program, uniform across input sizes and admissible
word widths. A successful certificate proves that this program terminates with
an output satisfying the mathematical specification, within a stated number of
RAM transitions. Source-level costs are derived from compiled machine execution;
there is no user `tick` primitive or arbitrary host-language computation escape.

The language includes expressions, named local variables, mutable word arrays,
structured control flow, ordinary first-order function calls, and recursion.
Every compiled operation is drawn from the same finite instruction set.

## Writing a function

```lean
import Ram.Syntax

open Ram Ram.DSL

def multiply : Func := ram_fun% (a, b) locals (answer) {
  answer := a * b;
  return answer;
}
```

The frontend assigns local register numbers. Programs contain no time ticks or
operation-price annotations. `ram% { ... }` also supports array reads/writes,
`if`, `while`, `read`, `write`, and `answer := call functionName(args);`.
Function names denote entries in a fixed function table. A return expression
comes at the end of a function; early return, break, and continue are not
constructs of the present language.

`Compiler.compileChecked` validates register bounds, function existence and
arity, then emits code. `Compiler.compileChecked_runs_measured` connects the
source execution to the exact full machine run. Its count includes the actual
stack-boundary input read and final halt. Runtime heap safety, sufficient stack
space, and representable return addresses are proof obligations, not hidden
runtime checks. Natural arithmetic specifications require appropriate range
proofs; without them multiplication and addition have modular word semantics.

## Proof interfaces and examples

- `Source.MeasuredExec` retains the compiler-derived exact count. Every safe
  source execution has such a derivation; it is not a user price annotation.
- `Source.Contract` combines total correctness with a proved budget. It has
  sequential composition and loop invariant/variant/potential rules, and a
  `compile` theorem connecting the budget to actual machine termination.
- `UniformTimeBound` and `UniformBigO` fix the program before quantifying over
  word widths and inputs. The asymptotic interface also requires correctness
  and termination for small inputs, below the asymptotic threshold.

Checked examples use the real compiler, not separate executable specifications:

- [Multiplication](Ram/Examples/Arithmetic.lean): a complete seven-step I/O run,
  with modular and no-overflow natural-number results.
- [Array sum](Ram/Examples/ArraySum.lean): `16 * length + 4` block transitions,
  plus one for halt. This contract starts with a preloaded array; it does not
  include an input loader or output writer.
- [Recursive factorial](Ram/Examples/Factorial.lean): a fixed 60-instruction
  program, `37 * k + 37` complete transitions, and proved factorial output.
  The linear bound is in the numeric value `k`, not its binary encoding length.

## Environment

Lean is pinned to **4.28.0-rc1**, matching the existing evaluation/search baseline.
The initial kernel uses Lean/Std only; introducing a newer CSLib or mathlib must
not silently change this baseline.

Compilation takes place on 0v0, in `/home/vvauted/ram-lean`, not on the user's
local computer. A normal checkout builds with `lake build` under the pinned Lean.

See [the design contract](docs/DESIGN.md),
[literature and architectural choices](docs/LITERATURE.md), and
[progress](docs/PROGRESS.md).
