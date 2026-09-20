/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Ram.AmortizedClear
import Examples.Ram.ArrayArguments
import Examples.Ram.ArrayCopy
import Examples.Ram.ArrayCopyFunction
import Examples.Ram.ArrayCount
import Examples.Ram.ArrayFold
import Examples.Ram.ArrayMap
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySliceProperties
import Examples.Ram.ArraySum
import Examples.Ram.BinarySearch
import Examples.Ram.BitLength
import Examples.Ram.Composition
import Examples.Ram.Factorial
import Examples.Ram.FactorialFunction
import Examples.Ram.FactorialStream
import Examples.Ram.FunctionComposition
import Examples.Ram.FunctionCompositionTime
import Examples.Ram.FunctionRun
import Examples.Ram.GraphDegree
import Examples.Ram.LocalBindings
import Examples.Ram.MergeSort
import Examples.Ram.Verification

/-!
# Writing direct word-RAM programs

[Getting started](ComplexityDocs/GettingStarted.html) · [Manual](ComplexityDocs.html)

This page describes the separately supported direct word-RAM interface.
Its word-level arithmetic and proof obligations differ from the
[high-level mathematical interface](ComplexityDocs/GettingStarted.html).

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
recursive calls. Arithmetic operates on words: multiplication wraps unless range hypotheses
justify its interpretation as natural-number multiplication. The default result is a word;
`: array` returns an `ArrayRef`, and `: Unit` returns no fields, using `return;`.
Return expressions occur at the end of functions; early return, `break` and `continue`
are not current constructs.

This is the function declaration from [the factorial example](##Examples.Ram.Factorial).
No `main`, input stream or output stream is required. `functions.function.factorial`
is the actual function; `functions.arguments.factorial` constructs its argument list
from typed word parameters. The same declaration also generates
`functions.eval.factorial`, `functions.bodyTime.factorial`, `functions.run.factorial`,
`functions.runTotal.factorial`, `functions.apply.factorial` and `functions.applyState.factorial`.
The [declaration interface](##Complexity.Computability.Ram.Source.Named.Declaration)
also exports lookup facts and source-local names for implementation proofs.
Generated body and return equations let verification unfold the same declaration.
These are execution and proof entry points, not automatic correctness proofs;
representation obligations depend on the chosen specification.

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
Generated value interfaces retain the declared result type: `Word w`, `ArrayRef w` or
`Unit`. These occupy one, two or zero return fields respectively. The raw function
execution and contract interfaces use lists of words, so a scalar result is `[value]`,
not a defaulted projection from a possibly empty list.
The shared [source-value interface](##Complexity.Computability.Ram.Source.Value) supplies
these representations. For proofs over typed arguments and results, use
`Ram.Source.TypedFunctionContract`; generated semantic values use `Ram.Func.evalTyped`.
`runTotal`, `apply` and `applyState` additionally take a final normal-termination proof `h`.
For the `squaredNorm` declaration above, the entry points are:

| Entry point | Result and meaning |
| --- | --- |
| `functions.eval.squaredNorm x y heapLimit entry` | `Part (Word w × Source.State w)`: the returned word and final shared state |
| `functions.bodyTime.squaredNorm x y heapLimit entry` | `Part Nat`: the same invocation's compiler-derived body count |
| `functions.run.squaredNorm x y heapLimit entry` | `Option (RunResult (Ram.State w))`: the complete compiled run, without an instruction limit |
| `functions.runTotal.squaredNorm x y heapLimit entry h` | `RunResult (Ram.State w)`: the same run, with normal halt proved |
| `functions.apply.squaredNorm x y heapLimit entry h` | `Word w`: that actual run's returned word |
| `functions.applyState.squaredNorm x y heapLimit entry h` | `Word w × Source.State w`: the returned word and reusable source shared state |

`eval` and `bodyTime` are noncomputable semantic observations, not executable Lean
functions. `run` executes the existing compiled call path. It retains the final machine
state, step count and stopping reason; it does not merely return a word or discard effects.
`runTotal` extracts the actual runner result with `Option.get`; `apply` decodes its
declared result, while `applyState` also recovers source shared state without private
target stack cells. The `Halts` proof is erased at runtime and requires normal halt, not
merely a nonempty `Option`. It supplies neither a reference answer nor a time budget.
All six refer to the same declared implementation. The explicit heap boundary and
entry state are not a time budget, and generating an entry point does not establish
code or stack capacity.

## Pass an existing array

An array parameter groups its base address and length. The
[array-sum implementation](##Complexity.Computability.Ram.Array.Sum) declares:

```lean
ram_def sumFunctions := ram_functions% {
  fn sum(xs : array) {
    let mut accumulator := 0;
    for x in xs {
      accumulator += x;
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
Its loop uses `for x in xs { accumulator += (x == target); }`. The
[sum runner](##Examples.Ram.ArraySum) and [count runner](##Examples.Ram.ArrayCount)
execute these same declared functions; `runCount` takes the target as a real word
argument, not an input-stream element or a proof-only constant.

`Ram.ArrayRef.Rep` connects a reference to the represented list and the heap boundary.
The sum contract proves the modular list sum and unchanged shared state. The pair contract
reuses it twice, without reopening the loop proof. Range and overflow premises still
belong to the operation contract. See [data models](ComplexityDocs/Models.html) for the
representation boundary and current limits on array-valued source expressions.

## Return and borrow an array

The [slice sample](##Examples.Ram.ArraySlice) returns a borrowed reference from one
function and passes that actual result to the existing sum implementation:

```lean
ram_def functions := ram_functions% {
  include sumFunctions as Sum;
  fn slice(xs : array, offset, count) : array {
    return subslice(xs, offset, count);
  }
  fn sumSlice(xs : array, offset, count) {
    let window ← call slice(xs, offset, count);
    let answer ← call Sum.sum(window);
    return answer;
  }
}
```

`subslice(xs, offset, count)` shifts the base by `offset` and sets the length to
`count`. Both descriptor fields are evaluated in the callee and received by the
caller through the ordinary compiled call. The address addition, return-field work
and call overhead are real instructions; no array elements are copied and no heap
storage is allocated.
The function contract requires containment and no-wrap conditions and
identifies the returned word with the sum of `(xs.drop offset.toNat).take count.toNat`.
`sumSlice_eq` states the corresponding ordinary executable natural-number value
modulo the word range, without a `main` or stream I/O.
The sample runs on preloaded `[1, 2, 3, 4, 5]` with offset `1` and count `3`,
returning `some (9, 243, Ram.StopReason.halted)`. Those 243 transitions include
both calls and descriptor work, but not host-side heap preparation.

Use `let other : array := window;` to copy a descriptor, or
`let window : array := array(base, length);` to construct one from word expressions.
`let window : array := subslice(xs, offset, count);` remains available for a local borrow.
An immutable binding forbids `window.base := ...` and `window.length := ...`, but
does not forbid writes such as `window[i] := value`; it is not read-only ownership.
`let mut window : array := ...;` permits descriptor-field updates. Copies refer to
the same heap, so updating cells through either handle affects the shared data.
Local handles also work with `for x in window` and typed array call arguments.

Typed array call positions accept `array(base, length)` and `subslice(xs, offset, count)`
directly. The first argument of `subslice` must be an already bound handle, optionally
parenthesized: use a prior `let` to construct or slice an intermediate handle.
These borrowed references are not general eager array expressions or checked slice
constructors. Array-valued returns use the same represented references, not loaded
Lean lists. Bounds and aliasing remain proof obligations; allocation and
automatic loading from Lean lists are still separate work.

## Call functions declared in another module

After importing modules containing earlier `ram_def` function declarations,
include their implementations under source aliases. The
[source-composition sample](##Examples.Ram.FunctionComposition) writes:

```lean
ram_def functions := ram_functions% {
  include copyFunctions as Copy;
  include sumFunctions as Sum;
  fn copyThenSum(source : array, destination : array) {
    call Copy.copy(source.base, destination.base, source.length);
    let answer ← call Sum.sum(destination);
    return answer;
  }
}
```

`call f(...);` executes a call for its effects without introducing a source name
for its result; `let _ ← call f(...);` is the explicit discard form.
Both work in scoped function and `main` bodies, including their nested blocks.
For a non-`Unit` result, the frontend allocates private destinations for its actual
fields. Here `Copy.copy` really declares `: Unit` and ends with `return;`: its call
has no result field or dummy destination. Neither discarding a result nor returning
`Unit` skips the function's shared-state effects or its actual call costs.
Raw `ram%` and `ram_stmt%` quotations have no inferred frame and require an explicit destination.

The earlier declarations' stored word/array signatures determine argument lowering:
`Copy.copy` takes three words, while `Sum.sum` takes one array reference. The frontend
links their function tables, relocates internal calls and appends the new functions.
These are imported source implementations, not Lean callbacks or duplicated loop bodies.
Imported aliases expose all six generated interfaces too, for example
`functions.eval.Sum.sumPair` and `functions.run.Sum.sumPair`. Includes require
`ram_def` and an earlier `ram_def` declaration; bare term quotations do not resolve them.

The generated `functions.applyState.copyThenSum` executes one compiled invocation
and returns its word and updated shared state. Its contract reuses copy and sum
contracts through generated embeddings; matching lengths, represented disjoint arrays
and sufficient code/stack capacity remain required. The mathematical result is the
modular sum and copied destination contents. A
[separate time proof](##Examples.Ram.FunctionCompositionTime) bounds that same invocation;
correctness and termination require no proposed time bound.
Its source-facing time tactics infer both call sites, including copy's empty
destination list. The proof supplies callee contracts, array facts and a bound for the
remaining sum call; it does not reconstruct either callee loop or local-register roles.
See [separate call costs](ComplexityDocs/Complexity.html) for that interface.

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

When the body also needs its position, use `for i, x in xs`. Both `i` and `x`
are immutable bindings local to the body; the zero-based index is a machine word.
The [in-place map sample](##Examples.Ram.ArrayMap) uses this form to write
`xs[i] := y` without declaring or incrementing its own counter. The compiler
emits the actual index initialization and increments, so they remain charged.
Shadowing a binder inside the body does not redirect those generated updates.

For this single-array scalar-call pattern,
`Ram.Source.Array.ForIn.function_contract` takes the generated body and return
equations, the helper's contract and the mathematical array premises. It infers
the private slots; a decidable layout fact replaces hand-written cursor setup.
The sample then uses an ordinary `List.foldl` identity to state its sum of squares.
The [expression rule](##Complexity.Computability.Ram.Array.ForIn.Expression)
`Ram.Source.Array.ForIn.Expression.function_contract` handles the sum and count
shape: one array first, optional additional word parameters, one initialized
accumulator and one expression update. It preserves those parameters, including
count's target, without a client-written cursor or parameter-preservation invariant.
The client still proves the actual expression's read safety and mathematical step.
The [separate cost rules](ComplexityDocs/Complexity.html) charge descriptor copies,
element bindings, expression instructions and real calls. Richer bodies, multiple
accumulators and short-circuiting still need further proof interfaces; general
source `for` syntax is not automatic loop verification or an arbitrary Lean compiler.

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
state independence by itself. The optional
[stream driver](ComplexityDocs/GettingStarted/Execution.html) is a separate program.

## Follow a complete proof

Start with the result equation in
[the function-value factorial sample](##Examples.Ram.FactorialFunction):
`eval_eq_factorial` states equality with mathlib's factorial when the result fits.
The left-hand side observes the implemented recursive function; it is not defined
to equal the mathematical specification. Its proof uses the function-only theorems
in [the factorial implementation](##Examples.Ram.Factorial). Read those in this order:

1. `Ram.Examples.Factorial.function_contract` proves the returned value and unchanged caller state
   by ordinary natural-number induction, using `ram_total_vc` and `ram_total_apply`.
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
The function's main correctness proof uses the smaller argument's contract directly,
without a separate recursive specification, local register names or stack-frame equations.
The induction and range/word-arithmetic facts are still explicit. Clients needing the
stronger function-body endpoint can use `recursive_total`, which proves local-state facts
separately; the independent cost proof still accounts for actual compiled calls.
This example does not supply automatic proofs of arbitrary recursion or a compiler for
ordinary Lean functions.
For optional native `StateM` verification, see [the increment example](##Examples.Ram.Verification).
Continue with [proving correctness](ComplexityDocs/Verification.html).

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
| Borrowing a local slice and calling an existing implementation | [Array slice](##Examples.Ram.ArraySlice) |
| Proving slice laws with ordinary list identities | [Slice properties](##Examples.Ram.ArraySliceProperties) |
| Composing calls with lexical value bindings | [Local bindings](##Examples.Ram.LocalBindings) |
| Reusing a list operation for a mathlib graph property | [Graph degree](##Examples.Ram.GraphDegree) |
| A logarithmic time bound | [Bit length](##Examples.Ram.BitLength) |
| Potential-based amortized analysis | [Amortized clearing](##Examples.Ram.AmortizedClear) |
| Reusing an array contract and its frame | [Array copy](##Examples.Ram.ArrayCopy) |
| Passing actual updated state to another call | [State-returning copy](##Examples.Ram.ArrayCopyFunction) |
| Calling imported implementations inside one source function | [Source composition](##Examples.Ram.FunctionComposition) |
| Lower bound with duplicates | [Binary search](##Examples.Ram.BinarySearch) |
| Recursive calls, borrowed arrays and a recurrence | [Merge sort](##Examples.Ram.MergeSort) |

These examples illustrate the current interfaces, including places that still require
representation and register-level proofs. The [roadmap](https://github.com/Vvauted/Complexity/blob/main/docs/ROADMAP.md)
focuses on removing that repeated work without changing the executable meaning.
-/
