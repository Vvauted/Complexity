/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Ram.ArrayArguments
import Examples.Ram.ArrayCopyFunction
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySum
import Examples.Ram.FactorialStream
import Examples.Ram.FunctionComposition
import Examples.Ram.FunctionRun
import Examples.Ram.GraphDegree
import Examples.Ram.LowerBound
import Examples.Ram.Merge
import Examples.Ram.MergeSort

/-!
# Executing direct word-RAM functions

[Getting started](ComplexityDocs/GettingStarted.html) · [Manual](ComplexityDocs.html)

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
data and arithmetic premises remain explicit. See [the proof interface](ComplexityDocs/Verification.html).

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
The source-level [FunctionComposition.copyThenSum](##Examples.Ram.FunctionComposition)
instead makes both calls inside one declared and compiled function.

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
mathematical representation. See [the backend](ComplexityDocs/Backend.html) for these boundaries.

For a ready-to-run demonstration, use the existing array-fill-and-sum driver:

```sh
lake exe ram-demo fast 1000
lake exe ram-demo reference 1000
```

Here `1000` is the array length; the driver computes the execution limit internally.
Both runners execute the same code and input. Their measured host runtimes are distinct
from the formal RAM transition count.
-/
