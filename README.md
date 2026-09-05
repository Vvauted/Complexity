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
For complete programs, `ram_program%` resolves function names automatically,
including forward calls and mutual recursion. Function names and local variables
have separate scopes; embedded `const(t)` terms retain their enclosing Lean scope.
A return expression comes at the end of a function; early return, break, and
continue are not constructs of the present language.

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

`exampleProgram.executable` checks and prepares the program once. Its `.run`
method accepts a transition budget and encoded input and returns the final
state, actual steps, and `halted`, `fault`, `invalidPC`, or `outOfFuel`.
The first input word is the compiler's heap/stack boundary, followed by the
program's input. The fast backend uses array code/registers and sparse tree-map
memory; its entire run result is proved equal to the reference machine.
The old `runExact` remains an exact-step mathematical interface, not the default
budget runner.

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
  assignment, store, I/O, branch and call rules, sequential composition and loop
  invariant/variant/potential rules. `RelContract` retains entry-state relations
  during composition. `compile_heap` transfers bounded heap observations as
  well as I/O to the actual halted machine, with a proved execution budget.
- `UniformTimeBound` and `UniformBigO` fix the program before quantifying over
  word widths and inputs. The asymptotic interface also requires correctness
  and termination for small inputs, below the asymptotic threshold.
- `Problem` fixes encoding, legal inputs, size and answers before submissions.
  Concrete-budget certificates support finite domains; asymptotic problems must
  supply arbitrarily large legal sizes. This does not replace semantic review of
  the problem's encoding and statement.

Checked examples use the real compiler, not separate executable specifications:

- [Multiplication](Ram/Examples/Arithmetic.lean): a complete seven-step I/O run,
  with modular and no-overflow natural-number results.
- [Array sum](Ram/Examples/ArraySum.lean): `16 * length + 4` block transitions,
  plus one for halt. This contract starts with a preloaded array; it does not
  include an input loader or output writer.
- [Recursive factorial](Ram/Examples/Factorial.lean): a fixed 60-instruction
  program, `37 * k + 37` complete transitions, and proved factorial output.
  The linear bound is in the numeric value `k`, not its binary encoding length.
- [Array fill](Ram/Examples/ContractFill.lean): public contracts prove a real
  input/output loop fills the target heap with ones within `14 * length + 9`
  transitions, including setup and halt.

## Running an example

On 0v0, `lake exe ram-demo fast 100000` runs a complete named array-write/sum
program. `reference` selects the original representation with identical code,
input and budget. The command reports the result, steps and execution time;
it is an example/measurement driver, not a pass/fail performance test suite.
See [measured results](docs/PERFORMANCE.md) for the workload and limits.

The optional [CSLib integration](docs/CSLIB.md) imports the official compatible
CSLib step-count relations and connects them to our exact execution and checked
compiler. It also connects proved machine bounds to mathlib's `IsBigO`; it does
not claim a RAM-to-Turing-machine simulation.

## Environment

Lean is pinned to **4.28.0-rc1**, matching the existing evaluation/search baseline.
The initial kernel uses Lean/Std only; introducing a newer CSLib or mathlib must
not silently change this baseline.

Compilation takes place on 0v0, in `/home/vvauted/ram-lean`, not on the user's
local computer. A normal checkout builds with `lake build` under the pinned Lean.

See [the design contract](docs/DESIGN.md),
[literature and architectural choices](docs/LITERATURE.md), and
[progress](docs/PROGRESS.md).
