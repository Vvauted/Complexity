/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

/-!
# Getting started

This page introduces function declarations, execution and proofs from one source program.
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
from typed word parameters. The same declaration also generates
`functions.eval.factorial`, `functions.bodyTime.factorial` and `functions.run.factorial`.
The [declaration interface](##Complexity.Computability.Ram.Source.Named.Declaration)
also exports lookup facts and source-local names for implementation proofs.
Generated body and return equations let verification unfold the same declaration.
These names do not yet hide every register-level obligation inside those proofs.

Locals may also be introduced where they are used. The
[function-composition sample](##Examples.Ram.LocalBindings) contains:

```lean
ram_def functions := ram_functions% {
  fn square(x) {
    return x * x;
  }
  fn squaredNorm(x, y) {
    let sx ← call square(x);
    let sy ← call square(y);
    return sx + sy;
  }
}
```

`let x := expression;` and `let x ← call f(...);` bind immutable local values;
`let mut` permits later assignment. Branch and loop locals stay inside their block,
and shadowing allocates a fresh slot without overwriting the old binding.
The frame size is inferred from the declarations. Array sum and count use `let mut`
for their accumulators. These remain first-order functions, not arbitrary Lean callbacks.
The sample separately proves a body count of 46: two real calls to `square`, each costing
23 transitions. The final `sx + sy` return expression and the enclosing call/return are
outside this body count and are charged when `squaredNorm` is called.

For a declaration named `p`, the generated entry points take the declared parameters
in order, followed by `heapLimit : Nat` and `entry : Ram.Source.State w`.
Word parameters take `Ram.Word w`; array parameters take `Ram.ArrayRef w`.
For the `squaredNorm` declaration above, the three views are:

| Entry point | Result and meaning |
| --- | --- |
| `functions.eval.squaredNorm x y heapLimit entry` | `Part (Word w × Source.State w)`: the returned word and final shared state |
| `functions.bodyTime.squaredNorm x y heapLimit entry` | `Part Nat`: the same invocation's compiler-derived body count |
| `functions.run.squaredNorm x y heapLimit entry` | `Option (RunResult (Ram.State w))`: the complete compiled run, without an instruction limit |

`eval` and `bodyTime` are noncomputable semantic observations, not executable Lean
functions. `run` executes the existing compiled call path. It retains the final machine
state, step count and stopping reason; it does not merely return a word or discard effects.
All three refer to the same declared implementation. The explicit heap boundary and
entry state are not a time budget, and generating an entry point does not establish
code or stack capacity.

## Pass an existing array

An array parameter groups its base address and length. The
[array-sum implementation](##Complexity.Computability.Ram.Array.Sum) declares:

```lean
ram_def sumFunctions := ram_functions% {
  fn sum(xs : array) {
    let mut accumulator := 0;
    while xs.length {
      accumulator := accumulator + load[xs.base];
      xs.base := xs.base + 1;
      xs.length := xs.length - 1;
    }
    return accumulator;
  }
  fn sumPair(left : array, right : array) {
    let leftSum ← call sum(left);
    let rightSum ← call sum(right);
    return leftSum + rightSum;
  }
}
```

`sumFunctions.arguments.sum` takes one `Ram.ArrayRef w`; the `sumPair` argument builder
takes two. So do the generated `sumFunctions.eval.sumPair left right heapLimit entry`
and `sumFunctions.run.sumPair left right heapLimit entry` entry points.
Each reference contains two words, `base` and `length`, passed through the
existing function ABI. The mathematical list of contents appears only in the contract.
Passing a reference does not allocate a descriptor, load a Lean list or copy array cells.
The calls above pass existing references and perform the actual array reads in `sum`.
Array and scalar parameters can be mixed: the
[counter](##Complexity.Computability.Ram.Array.Count) declares `fn count(xs : array, target)`.
Its generated argument builder takes an `ArrayRef` and one word, and its mathematical
contract identifies the decoded result with the ordinary `xs.count target`.

`Ram.ArrayRef.Rep` connects a reference to the represented list and the heap boundary.
The sum contract proves the modular list sum and unchanged shared state. The pair contract
reuses it twice, without reopening the loop proof. Range and overflow premises still
belong to the operation contract. See [data models](##ComplexityDocs.Models) for the
representation boundary and current limits on array-valued source expressions.

## Iterate with an element binding

The [array-fold sample](##Examples.Ram.ArrayFold) uses the same callable helpers
from the local-binding example:

```lean
fn sumSquares(xs : array) {
  let mut accumulator := 0;
  for x in xs {
    accumulator := call addSquare(accumulator, x);
  }
  return accumulator;
}
```

`for` copies the descriptor into private cursor locals and loads an immutable,
block-local `x` on each visit. Its generated control code does not advance `xs`
itself. Array contents are read during the traversal, not copied beforehand.
The same scoped block syntax supports local declarations, branches and calls.

For this single-array scalar-call pattern,
`Ram.Source.Array.ForIn.function_contract` takes the generated body and return
equations, the helper's contract and the mathematical array premises. It infers
the private slots; a decidable layout fact replaces hand-written cursor setup.
The sample then uses an ordinary `List.foldl` identity to state its sum of squares.
The [separate cost rule](##ComplexityDocs.Complexity) charges the descriptor copies,
element bindings and real calls. More general loop bodies still need their own
invariants and implementation proofs; this is not an arbitrary Lean compiler.

## State properties of a function value

The [local-binding sample](##Examples.Ram.LocalBindings) states its result directly
through the generated observation:

```lean
theorem squaredNorm_eval (heapLimit : Nat) (x y : Word w) (entry : Source.State w) :
    functions.eval.squaredNorm x y heapLimit entry = Part.some (x * x + y * y, entry)
```

This includes safe termination, the returned word and preservation of shared state.
The corresponding `squaredNorm_bodyTime` theorem separately observes `Part.some 46`.

[The function-value factorial sample](##Examples.Ram.FactorialFunction) exposes
the actual return value as `eval n` and its actual body count as `bodyTime n`.
These specialize `functions.eval.factorial n 0 (Source.State.initial [])` and
`functions.bodyTime.factorial n 0 (Source.State.initial [])`; the value view also
projects and decodes the returned word.
Its correctness theorem has the following mathematical shape:

```lean
theorem eval_eq_factorial (n : Word w) (hfit : Nat.factorial n.toNat < 2 ^ w) :
    eval n = Part.some (Nat.factorial n.toNat)
```

The equation includes termination. With this theorem, the sample proves positivity
using mathlib's `Nat.factorial_pos`, without carrying a source state in the proposition.
It separately proves `bodyTime n = Part.some (37 * n.toNat + 4)`, and connects both
observations to invocations at arbitrary caller states.

This uses mathlib's `Part` as a noncomputable semantic view, not a new interpreter.
It does not mean arbitrary ordinary Lean definitions can already be compiled by the library.
The underlying [function observations](##Complexity.Computability.Ram.Source.Function.Eval)
are defined from execution, independently of the mathematical factorial or its proposed cost.

Function arguments and return values are not stream input/output. The generic source state
also has `input` and `outputRev` fields so that functions which really use I/O can be modeled.
Their presence does not execute a `read` or `write`. Factorial's `function_runs` theorem
allows any initial input stream and existing output history, and proves the final shared
state is unchanged. `eval_eq_of_execution` shows that hiding this state in `eval n` did
not change the result at any actual caller. `Source.State.initial []` merely selects
a canonical empty-stream state; it neither inserts a read operation nor proves
state independence by itself. The optional driver below is a separate program.

## Execute a function without a driver

The [function runner sample](##Examples.Ram.FunctionRun) calls the generated
`Factorial.functions.run.factorial n 0 (Source.State.initial [])` entry point.
Its `runFactorialUntil` wrapper projects the full result to the returned word in
`result.state.regs 0`, `result.steps` and `result.reason`, decoding the word as a natural:

```lean
#eval runFactorialUntil (BitVec.ofNat 32 5)
-- some (120, 218, Ram.StopReason.halted)
```

The generated `run` uses `Ram.LocalCompiler.Function.runUntil`. It compiles a fixed
call-and-halt sequence and places runtime arguments in parameter registers. Argument
passing and result extraction are not stream operations; this factorial body also
performs no I/O. Other declared bodies may have stream effects, retained in the full result.
The 218 transitions include the enclosing call, return and halt, unlike the separate
function-body observation.
No time budget is supplied. The sample's `runFactorialUntil_eq` states its returned
value and exact count under the stack-capacity premise. For bounded exploration,
`runFactorial n limit` uses `Ram.LocalCompiler.Function.run` on the same code and
reports `outOfFuel` if its operational limit is reached.

The unbounded runner is executable, unlike the proof-only `Part` view. It uses Lean's
`partial_fixpoint` over the existing machine transition. A divergent program keeps running;
`Option` is not a runtime nontermination detector. Static compilation or arity failure can
return `none` from the function adapter, while a run that stops retains its stopping reason.
Inspect that reason before interpreting the result register as a successful return.

The [compiler bridge](##Complexity.Computability.Ram.Compiler.Local.Function)
relates the runtime value, visible shared state and step count to the function
proofs. Code and stack must fit the word address space. Heap contents are preloaded
explicitly, and host-side preparation is not counted as a RAM loader. Array references use
the generated word argument lists, but this adapter does not automatically turn arbitrary
Lean lists into loaded array data.
The [array-argument sample](##Examples.Ram.ArrayArguments) uses the generated
`sumFunctions.run.sumPair` on an explicitly prepared heap. Its mathematical list
concatenation describes the returned sum; no concatenated array or list loader is executed.

## Add an executable driver when needed

`Ram.Named.Functions.withMain` supplies an explicit entry statement without changing
the functions. A driver may read inputs and write results; ordinary function calls
and their correctness proofs do not require it. `ram_program%` remains available
when a complete program is the natural starting point.

The [factorial stream example](##Examples.Ram.FactorialStream) imports the independently
proved function and adds `read`, a call and `write`. The function implementation,
its mathematical value view and its direct runner do not import this driver.

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

Start with the result equation in
[the function-value factorial sample](##Examples.Ram.FactorialFunction):
`eval_eq_factorial` states equality with mathlib's factorial when the result fits.
The left-hand side observes the implemented recursive function; it is not defined
to equal the mathematical specification. Its proof uses the function-only theorems
in [the factorial implementation](##Examples.Ram.Factorial). Read those in this order:

1. `Ram.Examples.Factorial.function_contract` states the returned value and unchanged caller state.
2. `Ram.Examples.Factorial.function_runs` gives a safe invocation with an explicit argument.
3. `Ram.Examples.Factorial.function_result` identifies the returned natural number with
   mathlib's factorial when the result fits in a word.
4. `Ram.Examples.Factorial.function_timeBound` separately bounds the same body's execution.

The separate [stream-driver module](##Examples.Ram.FactorialStream) imports that
function and its proofs. Its `runs` theorem includes the `read`/`write` adapter and
all machine overhead; it is not a prerequisite for the function interface above.
The no-stream compiled application is illustrated in
[the function runner](##Examples.Ram.FunctionRun).

The general result is factorial modulo the word range, not unbounded arithmetic.
The source-level recursive proof still needs local representation facts; the public
function contract does not expose those registers to its callers.
For optional native `StateM` verification, see [the increment example](##Examples.Ram.Verification).
Continue with [proving correctness](##ComplexityDocs.Verification).

## Choose a larger example

| What you want to study | Example |
| --- | --- |
| Linking independently verified programs | [Composition](##Examples.Ram.Composition) |
| Array traversal and an ordinary list model | [Array sum](##Examples.Ram.ArraySum) |
| Reusing a fold and ordinary permutation invariance | [Array count](##Examples.Ram.ArrayCount) |
| Calling a proved function at each array element | [Call-based fold](##Examples.Ram.ArrayFold) |
| Recursive mathematical specifications | [Factorial](##Examples.Ram.Factorial) |
| Function-value equations and separate cost observations | [Factorial function](##Examples.Ram.FactorialFunction) |
| Executing a function with no input/output main | [Function runner](##Examples.Ram.FunctionRun) |
| Adding stream I/O around a proved function | [Factorial stream driver](##Examples.Ram.FactorialStream) |
| Typed array calls on explicitly preloaded data | [Array arguments](##Examples.Ram.ArrayArguments) |
| Composing calls with lexical value bindings | [Local bindings](##Examples.Ram.LocalBindings) |
| Reusing a list operation for a mathlib graph property | [Graph degree](##Examples.Ram.GraphDegree) |
| A logarithmic time bound | [Bit length](##Examples.Ram.BitLength) |
| Potential-based amortized analysis | [Amortized clearing](##Examples.Ram.AmortizedClear) |
| Reusing an array contract and its frame | [Array copy](##Examples.Ram.ArrayCopy) |
| Lower bound with duplicates | [Binary search](##Examples.Ram.BinarySearch) |
| Recursive calls, borrowed arrays and a recurrence | [Merge sort](##Examples.Ram.MergeSort) |

These examples illustrate the current interfaces, including places that still require
representation and register-level proofs. The [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md)
focuses on removing that repeated work without changing the executable meaning.
-/
