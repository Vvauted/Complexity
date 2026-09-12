/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples

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

The [typed frontend](##Complexity.Language.Syntax) supports ordinary parameters,
local variables, calls and recursion. `(pure)` also generates an executable
native Lean function from the same body:

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

Finite-range loops can also generate an ordinary total function:

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
in one `source_program (pure)` declaration. Its correctness theorem is the
ordinary equation `Structured.run n limit = min (n + 1) limit`.
The generated `Structured.run_refines.of_math` transfers that mathematical proof
to the same source implementation; the
[compiled client](##Examples.Language.ScalarCompiled) proves its actual RAM
result and independent instruction bound using shared range and cost rules.
This structure path currently supports closed structures with direct scalar or
scalar-product fields, not arbitrary Lean datatypes or dependent fields.
The same scalar file also keeps such a structure as a finite-range accumulator,
calling a structure-valued helper in each round with a dynamic positive stride.
`StructuredRange.sum` has an ordinary fold/sum proof and generated total source
contract. Its complete function-body instruction bound reuses generated native
guard/body equations and the shared range cost rule, without hand-written
capture indices or a second round-count proof. Finite-word realization and a
halted RAM invocation for this loop remain open; general loops and recursive
calls over registered structures remain unsupported.

Products and options are ordinary values too. The
[structured client](##Examples.Language.OptionalBuffer) imports a helper returning
`Option (Nat × Nat)`, then returns a length and optional borrowed buffer to its
caller. Ordinary bindings such as `let (length, present) ← Library.inspect xs`
and patterns such as `some (length, offset)` destructure that same actual result;
the right-hand side is evaluated once. That caller modifies the first cell only when
present. Its specification uses an ordinary `Array.modify` result and preservation
of outside views, not register identities. Effectful programs use mathematical
contracts rather than pretending that borrowed mutation is a pure operation.

The [high-level proof guide](##ComplexityDocs.Verification) explains both modes.
The pure subset supports scalars and their products/options, finite-range `for`,
self-recursion and acyclic calls. General pure `while`, mutually recursive pure
families and buffers remain unsupported.
General effectful declarations support `while`, bounded `for`, borrowed buffers, allocation and
scoped scratch reclamation. This is a checked executable subset, not a compiler
for arbitrary Lean definitions.

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

## State a correctness-and-complexity task

The [fixed-type interface](##Complexity.Program.Basic) separates a mathematical
input/output requirement from a bound on the same compiled implementation:

```lean
def Task : Prop :=
  ∃ solve : Complexity.Program (Array Nat) Nat,
    solve.Correct isLegal (fun cards result => result = answer cards) ∧
    solve.TimeO isLegal Array.size (fun n => n + 1)
```

`solve` is a source program, not an arbitrary Lean function or a record
containing its own desired answer. `Correct` takes an ordinary input/output
relation, so a task can describe acceptable results without selecting one
reference algorithm. `TimeO` separately takes the input-size function and
growth bound. Both obligations refer to this same `solve`.

The [typed-program example](##Examples.Language.Program) selects the existing
bounded-increment declaration as `Program (Nat × Nat) Nat`. Its proof applies
`Program.Correct.of_functionTotal` to the generated source contract, then reuses
the ordinary minimum equation. This keeps invocation and evaluation bookkeeping
in the library; it does not require another implementation or argument adapter.

The [input instances](##Complexity.Program.Input) supply scalars, a natural
array, and right-associated scalar prefixes such as `Nat × Array Nat` as
separate source parameters. Results include scalars, natural arrays, products
and options. Task authors fix these conventions before choosing a candidate.
An ordinary record can be registered through an injective field presentation;
that registration is not automatic support for record syntax in the frontend.
General products of independently heap-backed inputs still need a shared layout.

The [RAM interface](##Complexity.Computability.Ram.Compiler.Language.Program)
requires actual halted executions uniformly over all admitted word widths.
The width rule is a fixed constant multiple of logarithmic input size/value
width; capacity is established inside the execution proof, not used as a
precondition excluding inconvenient inputs. The shared `TimeO.runs_correct`
rule combines the mathematical postcondition and instruction bound on one
execution. Inputs are preloaded; an executable loader is not silently included.
Correctness remains independent of word widths and time budgets.

The
[compatibility bridge](##Complexity.Computability.Ram.Compiler.Language.Program.ArrayFunction)
preserves source correctness and actual RAM time for existing
`ArrayFunction` clients viewed as `Program (Array Nat) Nat`; it does not require
another algorithm proof.

## Work directly with word-RAM source

The rest of this page describes the separately supported direct word-RAM
interface. Its word-level arithmetic and proof obligations differ from the
high-level mathematical Nat interface above.

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
belong to the operation contract. See [data models](##ComplexityDocs.Models) for the
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
See [separate call costs](##ComplexityDocs.Complexity) for that interface.

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
The [separate cost rules](##ComplexityDocs.Complexity) charge descriptor copies,
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
For this raw `run` interface, inspect that reason before interpreting the result
register as a successful return; a fault can also produce `some result`.

The [compiler bridge](##Complexity.Computability.Ram.Compiler.Local.Function)
relates the runtime value, visible shared state and step count to the function
proofs. Code and stack must fit the word address space. Heap contents are preloaded
explicitly, and host-side preparation is not counted as a RAM loader. Array references use
the generated word argument lists, but this adapter does not automatically turn arbitrary
Lean lists into loaded array data.
The [array-argument sample](##Examples.Ram.ArrayArguments) uses the generated
`sumFunctions.run.sumPair` on an explicitly prepared heap. Its mathematical list
concatenation describes the returned sum; no concatenated array or list loader is executed.

## Use an ordinary executable value

With normal termination proved, `p.apply.f ... heapLimit entry h` returns the declared
word, array reference or `Unit` without `Part` or `Option` in its result type. The
[function runner sample](##Examples.Ram.FunctionRun) defines an ordinary
`factorial n hstack : Nat` by decoding this word:

```lean
#eval Ram.Examples.FunctionRun.factorial (BitVec.ofNat 32 5) (by decide)
-- 120
```

Here `n : Word 32` is the only runtime argument. The erased `hstack` proof establishes
`(n.toNat + 1) * ABI.frameSize Factorial.functions.registers < 2 ^ 32`.
`factorial_eq_mod` identifies the result modulo the word range; `factorial_eq` and
`factorial_pos` additionally require that the mathematical factorial fits in 32 bits.
No result specification or instruction bound is an argument to the function.
Its independent `factorial_steps` theorem observes the same full run through `runTotal`.

The [array-sum sample](##Examples.Ram.ArraySum) similarly defines
`sum array heapLimit entry safe hstack : Nat`. Its data inputs are an `ArrayRef 32`,
the heap boundary and the preloaded state. The mathematical list appears only in
the erased `safe` proof of representation and non-wrapping addresses, not as an
extra runtime argument. The separate `hstack` proof supplies room for the call frame
below `2 ^ 32`. `sum_eq` gives the modular list sum; `sum_eq_of_sum_lt`
recovers the exact natural sum when it fits. The
[graph-degree client](##Examples.Ram.GraphDegree) reuses this ordinary value equation
to prove `sum_eq_degree`, without reopening the implementation's loop or call frame.

The [lower-bound sample](##Examples.Ram.LowerBound) also provides an ordinary
`lowerBound array key heapLimit entry safe hstack : Nat`. Its value theorem states
that this executable result equals
`xs.findIdx (fun x => decide (key.toNat ≤ x.toNat))`. The borrowed array must
represent the sorted list; an absent key returns its insertion position, possibly
`xs.length`. Empty arrays and repeated values need no special interface.
The [function declaration](##Complexity.Computability.Ram.Array.Search.Function)
uses ordinary `lo` and `hi` locals and a loop-scoped `mid`; it neither consumes
an input stream nor writes an output stream. Its separate `runTotal_steps_le`
bounds the complete invocation by `25 * Nat.clog 2 (xs.length + 1) + 69`,
including the real call, return and halt but not host-side memory loading.
The implementation proof remains more detailed than this client equation:
it establishes the sorted interval invariant, safe word arithmetic and termination.

For mutation, the [merge sample](##Examples.Ram.Merge) provides
`Function.merge left right destination heapLimit entry safe hstack`, returning
the actual shared state of a three-array, `Unit`-returning call.
`Function.merge_contents` equates its destination contents to standard `List.merge`;
`Function.merge_sorted` derives a sorted permutation when the sources are sorted.
The source arrays may overlap each other, but the destination must be disjoint
from each and its view must have exactly their combined length. This is existing
storage, not an allocation. The separate full-run bound is
`34 * (xs.length + ys.length) + 122`, including the wrapper's actual core call,
its own calling convention and halt.

The [recursive-sort sample](##Examples.Ram.MergeSort) now also provides
`Function.sort array scratch heapLimit entry safe hstack`. Its declaration takes
two array references and returns `Unit`, recursively calls itself on slices,
then actually calls merge and copy. The returned shared state contains the
sorted input: `Function.sort_sorted` states the ordinary sorted-permutation
property, and `Function.sort_stateM` identifies the same contents with the
existing list-state model. The source and scratch views must be disjoint and
equally sized. This is a proved function over pre-existing storage, not an
unimplemented `List → List` loader or an invocation of the host-side sort.
Its separate `Function.runTotal_steps_le` bounds that actual invocation by
`Recurrence.balancedBudget 4 227 xs.length + 81`, an `n log n` reserve including
recursive calls, merge, copy and the outer halt. Correctness and normal
termination are established without supplying this bound to the program.

Factorial, sum and the [slice sample](##Examples.Ram.ArraySlice) use
`ram_run_apply theorem [facts]` to connect their function proofs to these executable values.
This use-site tactic applies an existing runtime theorem and checks the standard
compiled call's static obligations;
the clients need no separate raw-code definition or compilation/code-fit lemmas.
`halts_of_contract` reuses a budget-free function contract, while `hstack`, represented
data and arithmetic premises remain explicit. See [the proof interface](##ComplexityDocs.Verification).

These functions execute the existing compiled RAM call, not `Part.get` or a
mathematical reference function. They work with `#eval`, but the underlying
partial-fixed-point runner is not an ordinary kernel-reducing recursive definition:
use the proved value equations, not an expectation that `rfl` computes a result.
This adds executable application of declared source functions, not compilation of
arbitrary Lean definitions. Use `applyState` for shared state usable by another call,
or `runTotal` for the complete machine result and actual steps. Projecting a result
with `apply` does not prove shared state unchanged.

The [state-returning copy sample](##Examples.Ram.ArrayCopyFunction) defines
`copy source destination length heapLimit entry safe hstack : Source.State 32`.
It projects the state from the real `Unit × Source.State 32` result of copy's
generated `applyState`. It executes the existing copy function's stores;
`copy_contents` identifies the copied destination using the existing `arrayContents` observation. Its
`ArrayCopyFunction.copyThenSum` passes that returned state to the ordinary sum function.
This is host-side sequencing of two real compiled calls, not one newly compiled RAM
function, and has no combined RAM-cost theorem. Representation, disjointness and
capacity remain explicit.
The source-level `FunctionComposition.copyThenSum` above instead makes both calls
inside one declared and compiled function.

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
