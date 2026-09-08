/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

/-!
# Proving complexity

A useful complexity proof has two parts: show what work the program performs, then bound
that work mathematically. The compiler and operation contracts supply the first connection;
ordinary Lean functions and mathlib supply the sums, recurrences and asymptotics.

## Keep correctness separate

For a callable function, `Ram.Source.FunctionMeasuredExec` observes both its actual
returned value and its compiled body count. `Ram.Source.FunctionTimeBound` bounds
that count separately from `Ram.Source.FunctionContract`; combine them with
`Ram.Source.FunctionContract.with_timeBound` when a bounded invocation is needed.
The body count includes nested calls, but excludes the enclosing call site's argument
evaluation and frame/return sequence. `Ram.Source.FunctionMeasuredExec.call` adds
those exact generated costs. A body bound alone is not the whole call's time.

`Ram.Source.TimeBound` bounds every completed measured execution satisfying its precondition.
It does not assert that one exists. Prove safe total correctness independently, then combine
the results with `Ram.Source.TotalContract.with_timeBound`. Both proofs describe the same
statement and execution.

Use `Ram.Source.TimeBound.seq` to compose bounds. The second bound is evaluated at the actual
intermediate state; the first block's total contract supplies the facts needed there.
Branches, calls and recursive specifications have corresponding rules. Changing a bound
does not require changing the functional postcondition.

For a straight-line block, `Ram.Source.TimeBound.of_isStraightLine` derives the exact
compiled-code-length bound without repeating its correctness proof. Branches, loops and
calls need their own rules: their code length is not their execution length.

See [time bounds](##Complexity.Computability.Ram.Verification.Time.Basic) and
[straight-line costs](##Complexity.Computability.Ram.Verification.Time.StraightLine).

## Keep actual steps with ordinary application

The executable `p.apply.f` returns a word from `p.runTotal.f`; the latter retains
the actual machine result and its `steps`. Their normal-halt proof supplies neither
a step formula nor an execution limit and is erased at runtime.
`Ram.LocalCompiler.Function.runTotal_steps_eq_of_execution` combines the independent
function execution and body-time equation to identify those same full-run steps.
The [factorial sample](##Examples.Ram.FunctionRun) uses `factorial_steps` to identify
`37 * n.toNat + 33` steps; the [sum sample](##Examples.Ram.ArraySum) uses `runTotal_steps`
to identify `18 * xs.length + 67`. These include the enclosing call, return and halt.
The wrappers do not change the RAM trace or price host-side work as RAM instructions;
they execute that trace and project its result. `Part` body-time observations remain
noncomputable proof views, separate from this executable application.

## Count an expression-based array fold

`Ram.Source.Array.ForIn.Expression.function_measured` recovers an exact count
from the same completed function execution as its budget-free correctness proof.
Its `function_bodyTime` consequence observes that count through `Part`.
For an update expression compiling to `E` instructions, the body count is
`(E + 15) * n + 8`. This includes assignment, actual element loads and bindings,
cursor updates, guards, accumulator initialization and both descriptor copies.
The expression's instruction length comes from compilation, not a supplied price.

The [sum](##Examples.Ram.ArraySum) and [count](##Examples.Ram.ArrayCount) clients
reuse this rule and the actual compiled-call bridge:

| Declared function | Body steps | Full invocation, including halt |
| --- | --- | --- |
| `sum(xs)` | `18 * n + 8` | `18 * n + 67` |
| `count(xs, target)` | `20 * n + 8` | `20 * n + 76` |

Count passes its target as an additional runtime word parameter; parameter and
frame instructions are part of its full count. These runners execute the declared
functions, not the noncomputable `Part` observations. Input representation and
stack capacity remain premises, and host-side preloading is not a counted RAM loader.

## Compose function costs

The [two-array example](##Examples.Ram.ArrayArguments) calls the existing `sum`
function twice. For represented lists of lengths `n` and `m`, the sum body takes
`18 * n + 8` steps. Its call site adds 58 steps derived from the actual argument,
frame and return instruction blocks. Thus the pair body has exact count

```text
(18 * n + 8 + 58) + (18 * m + 8 + 58) = 18 * (n + m) + 132
```

`Ram.Source.Array.sumPair_bodyTime_eq` proves that equation about the program's
own time observation. It reuses the sum proof rather than redoing the loop.
The independent correctness contract supplies the returned list sum and unchanged
shared state, with no proposed time bound.

The executable `runSumPair_eq` theorem also counts the outer pair invocation and
final halt, obtaining `18 * (n + m) + 197` for the same returned value. The runtime
call takes no instruction limit. The represented input heap and sufficient code
and stack capacity remain explicit; loading or concatenating the lists is not
part of this program. Concatenation appears only in its mathematical specification.

`Ram.LocalCompiler.Function.runUntil_eq_of_execution` joins the independently
proved function execution and body-time equation into an exact executable-call
theorem. Determinism identifies the measured count with that same invocation.
`Ram.LocalCompiler.Function.callSteps_eq` then reduces the outer call overhead
using generated code lengths, the declared parameter count and frame size.
Neither lemma supplies an unproved cost or removes the stack-capacity premise.

## Count calls inside an array fold

`Ram.Source.Array.ForIn.function_bodyTime` observes the same completed invocation
established by the budget-free function contract. For its single-array, scalar-accumulator,
fixed-helper shape, it requires a proof that every completed helper-body execution has
the constant count `bodySteps`. `Fold.Call.callSteps` includes that body, evaluated
arguments, frame handling and the return expression. The function-body count is
`(callSteps + 14) * n + 8`: each iteration includes the element load and binding,
cursor updates, guard and back edge. The constant term includes accumulator
initialization, both descriptor copies and the final false guard, also for an empty array.

In [the array-fold sample](##Examples.Ram.ArrayFold), `sumSquares` calls `addSquare`
for each word, and `addSquare` calls the existing `square`. The separate helper-body
proof gives 23 steps; its complete call on the accumulator and loaded element takes 62.
Thus `bodyTime_eq` gives `76 * n + 8` for the function body.
`runSumSquares_eq` adds the outer call, return and halt, giving `76 * n + 67` on
the same represented input. These are real compiled calls, not priced mathematical
callbacks. The outer frame includes the three private iteration locals; those slots
are not free merely because the source syntax hides them. Code and stack must fit,
and host-side heap preloading is not a RAM loader included in this count.

This specialized rule covers constant callee-body counts. Data-dependent step costs
are not yet packaged as a dedicated call-fold rule; use the general time-bound and
loop-composition interfaces below. The mathematical `List.foldl` view supplies neither
free execution nor a cost annotation. The lower-level `Fold.Call.loop_localMeasured`
still describes its explicit cursor loop, without the `for` descriptor copies
and element-binding step; that count is not the current `sumSquares` body count.

## Choose the argument that matches the loop

Supply the invariant and progress facts from the correctness proof. The available rules
cover several common forms of remaining work:

| Argument | Rule or module |
| --- | --- |
| A decreasing natural variant and constant body bound | `Ram.Source.TimeBound.while_linear` |
| Body work depending on the current variant | [finite-sum loops](##Complexity.Computability.Ram.Verification.Loop.Sum) |
| A positive measure decreases by a factor greater than one | [logarithmic loops](##Complexity.Computability.Ram.Verification.Loop.Logarithmic) |
| A list of actual visits, including repetitions | [traversal rules](##Complexity.Computability.Ram.Verification.Loop.Traversal) |
| Work creates further tasks | [worklists](##Complexity.Computability.Ram.Verification.Amortized.Worklist) |

For a linear loop, let `G` be the compiled guard and conditional-branch cost, `B` the
body bound and `v` the initial variant. The derived bound is

```text
v * (G + B + 1) + G
```

The back edge and final false guard are included, also when the body never runs.
List traversal counts occurrences rather than distinct values. Queue manipulation, address
calculation and any generated work must be part of the implemented body.

## Amortized analysis

`Ram.Source.AmortizedContract` relates actual work to a charge and endpoint potentials:

```text
actualSteps + potential(final) ≤ charge(entry) + potential(entry)
```

Composition cancels the intermediate potential. Keep the final credit when it will pay for
later work, and include initial credit when exporting an ordinary bound. A potential does
not make the construction of a preexisting data structure free.

The [potential rules](##Complexity.Computability.Ram.Verification.Amortized.Potential)
describe how to change or combine potentials. A change needs an endpoint inequality;
pointwise ordering of two potentials alone is insufficient.
[Amortized traversal](##Complexity.Computability.Ram.Verification.Amortized.Traversal)
and [worklists](##Complexity.Computability.Ram.Verification.Amortized.Worklist) retain
the credit needed for subsequent operations.

For a numerical history independent of RAM, use
`Finset.sum_range_add_potential_le` in [amortized sums](##Complexity.Analysis.Amortized).
It telescopes the corresponding one-step inequalities over a finite range.

## Solve the numerical recurrence

First justify the recursive calls and nonrecursive work of the implementation.
The `Recurrence` namespace then analyzes a numerical bound; it does not supply a missing
execution or termination argument.

For balanced splitting, `Recurrence.le_nlogn_of_balanced_le` accepts bounds of the form

```text
T(0), T(1) ≤ a
T(n) ≤ T(n / 2) + T(n - n / 2) + c * n    for n ≥ 2
```

and proves `T(n) ≤ a * max(1, n) + c * n * Nat.clog 2 n`.
Odd sizes and both base cases are included; `T` need not be monotone.
The [balanced recurrence module](##Complexity.Computability.Recurrence.Balanced) also exports
a mathlib Big-O theorem. The existing merge-sort development uses this analysis.

Other entry points are [successor and dividing recurrences](##Complexity.Computability.Recurrence.Basic)
and [finite branching](##Complexity.Computability.Recurrence.Finite).
For unequal branching, the [Akra–Bazzi bridge](##Complexity.Computability.Recurrence.AkraBazzi)
and [majorant construction](##Complexity.Computability.Recurrence.Majorant) reuse mathlib,
including its regularity and rounding hypotheses. Power-toll and rounding lemmas are in
[Growth](##Complexity.Computability.Recurrence.Growth),
[Supercritical](##Complexity.Computability.Recurrence.Supercritical) and
[Rounding](##Complexity.Computability.Recurrence.Rounding).

An upper recurrence yields an upper bound. It does not justify a matching lower bound
or a tight Theta claim without additional information.

## Use mathlib asymptotics directly

The library uses `Asymptotics.IsBigO`, not a second Big-O definition.
`Asymptotics.IsPolynomiallyBounded` packages an existential polynomial upper bound and has
closure rules for sums, products, powers and composition.
Its [polynomial-growth interface](##Complexity.Analysis.Asymptotics.Polynomial) can extract
an all-input natural bound, accounting for the finite prefix below an asymptotic threshold.

For a varying set of terms, use [uniform finite sums](##Complexity.Analysis.Asymptotics.Sum)
or [list traversal sums](##Complexity.Analysis.Asymptotics.Traversal).
One uniform coefficient and threshold must cover all terms selected at that input.
Separate per-index Big-O statements are insufficient when their constants grow with the index.

`Ram.UniformBigO` connects actual runtime witnesses to a scalar growth expression.
`Ram.UniformBigOAt` additionally makes the growth regime explicit through a filter.
For several parameters, choose the filter that describes the intended legal inputs;
product `atTop` would require each parameter to grow.
[Reparameterization](##Complexity.Computability.Ram.Time.Reparam) changes the mathematical
size coordinate through a proved limit and comparison, not by executing a data conversion.

## Compose implementations, then state the complete claim

`Ram.TotalComponent.comp` links independently verified programs before choosing time bounds.
Its `Ram.TotalComponent.TimeBoundOn.comp` rule then adds separate conditional costs at the
actual intermediate input. Once a scalar input-size envelope has been proved,
`Ram.TotalComponent.withTimeBound` retains the same code when exporting to the existing
resource-aware `Ram.Component` interface.

`Ram.Component.comp` also links already costed source programs and function tables, including
recursive calls. Shared representations connect the first result to the second input.
`Ram.Component.TimeBoundOn` and `Ram.Component.ResourceBoundOn` support bounds depending
on the full input; composition uses the actual intermediate value `f x`.

For scalar envelopes, composition uses the intermediate output-size bound and
`Asymptotics.monotoneHull` to control a potentially nonmonotone downstream bound.
Time adds; sufficient heap and call-depth capacities combine by maximum.
An implemented representation adapter has its own cost, while a proof-only change of
mathematical view executes nothing.

`Ram.PolyTimeComponent` also carries a polynomial output-size bound, so repeated polynomial
composition is justified. [Executable reductions](##Complexity.Computability.Ram.Reduction)
reuse that program composition. These are results for the specified word-RAM.

There are three distinct levels of claim:

| Level | What the proof supplies |
| --- | --- |
| A numerical bound | Growth of an ordinary function |
| A verified component | Program behavior and bounds under its representation and domain |
| A fixed-problem certificate | Complete execution on every original legal input |

`Ram.Component.Realization` connects a component to a previously fixed problem's encoding,
legal widths, capacities and output observations. `Ram.Certificate` then states the
complete concrete bound. Asymptotic certificates also require a nontrivial growth regime.
The whole-program entry adds the real header-read and halt overhead.

See [realization](##Complexity.Computability.Ram.Component.Realization) and
[problem certificates](##Complexity.Computability.Ram.Problem.Asymptotics).
A preloaded-array theorem does not silently include an input loader.
A RAM certificate does not by itself establish a bit-cost or Turing-machine complexity result.

## Reading existing proofs

Start with [bit length](##Examples.Ram.BitLength) for a logarithmic bound,
[amortized clearing](##Examples.Ram.AmortizedClear) for a potential argument, or
[merge sort](##Examples.Ram.MergeSort) for recursive composition and a balanced recurrence.

Some existing proofs use the coupled `ram_vc` and `ram_apply` interfaces.
Their budget is threaded through execution, not restarted at each statement.
`ram_bound [facts]` simplifies proved cost expressions using ordinary arithmetic.
These tools remain useful, but a new functional specification need not expose their budget.
-/
