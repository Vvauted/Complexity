/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Understanding the backend

The word-RAM gives an execution meaning to the source language and its resource contracts.
Algorithm proofs should normally use the [verification](##ComplexityDocs.Verification) and
[data-model](##ComplexityDocs.Models) interfaces. This chapter explains what those proofs
ultimately guarantee, and which machine assumptions remain visible.

## What counts as one step?

`Ram.Instr` fixes the instruction vocabulary. A word is `BitVec w`; addition, subtraction
and multiplication wrap modulo `2^w`. Division and remainder use Lean's unsigned conventions,
including `x / 0 = 0` and `x % 0 = x`. An exact natural-number interpretation requires the
corresponding range hypotheses. See [word operations](##Complexity.Computability.Ram.Word).

Every `some` result of `Ram.step` counts as one transition. This includes a halt instruction
and an input read that enters the fault state. `Ram.Exec` records the exact count;
`Ram.TerminatesWithin` additionally requires a genuinely halted endpoint, so a fault,
invalid program counter or exhausted runner budget is not successful termination.

Word multiplication and division each take one machine transition. This is the chosen
word-RAM model, not a statement about arbitrary-precision arithmetic or bit complexity.
The register names and program counter are naturals in the semantics; a fixed finite program
uses finitely many registers, while stored values and memory addresses are words.

The [bounded runner](##Complexity.Computability.Ram.Execution.Runner) agrees with this
semantics. The [unbounded runner](##Complexity.Computability.Ram.Execution.Unbounded)
uses the same transition without a supplied limit. `Ram.runUntil_halted_iff` identifies
its returned halted results with finite `Exec` derivations and the exact same count.
`Ram.Fast.map_run` relates the optimized bounded executable representation to the reference
one. Their host runtimes can differ; neither runtime defines the formal transition cost.

`Ram.runUntil` uses executable `partial_fixpoint` recursion. Halt, fault and invalid PC
return `some` with the appropriate stopping reason; it cannot return `outOfFuel`.
Divergence is the logical bottom value `none`, not a runtime detection algorithm: a
divergent program keeps executing. The bounded runner remains useful for exploratory
execution which must stop after a chosen number of transitions.

## From source proof to halted execution

The source language has fixed expression and statement constructors. A mathematical function,
loop invariant or potential used in a proof is not an executable source primitive.

The verified path has three layers:

1. `Ram.Source.SafeExec` records source execution with safe accesses, available input and
   sufficient call depth. Total correctness supplies such an execution without a time budget.
2. `Ram.Source.LocalMeasuredExec` records the count derived from the emitted instructions.
   Its rules cover structured control flow and recursive calls.
3. `Ram.LocalCompiler.compileChecked_runs_measured_heap` connects that execution to the
   checked target program, retaining the visible heap and I/O at a halted endpoint.

`Ram.LocalCompiler.compileChecked` checks static register bounds, function lookup and arity.
Runtime safety and capacity are premises of the compiler theorem, not automatically inserted
bounds checks. Successful compilation alone therefore does not establish correctness.

For the whole-program entry point, the actual input begins with a heap-boundary header.
The target reads that header and executes a final halt, adding two transitions to the measured
source body. A preloaded block theorem instead requires an explicit matching initial state;
its bound does not silently include unspecified input preparation.

Start with [execution export](##Complexity.Computability.Ram.Verification.Execution) for client
theorems or [whole-program compilation](##Complexity.Computability.Ram.Compiler.Local.Program.Basic)
for the underlying simulation.

## Call a function without stream I/O

`Ram.LocalCompiler.Function.runUntil` executes a checked fixed call-and-halt trampoline.
Runtime argument words are preloaded in parameter registers; the initial program counter
is 1 and the stack pointer is the explicit heap boundary. This entry skips the linker's
header-read instruction. It neither consumes an input word to pass a function argument
nor writes an output word to return a result. The function body may still contain its own
I/O operations, and those effects are retained.

`Ram.Source.FunctionExec` observes the function's returned word separately from shared
state. The source state's `input` and `outputRev` fields model possible stream effects;
they are not implicit operations. For example, factorial proves the same result for
arbitrary caller streams and preserves them. Its optional stream main actually executes
`read` and `write`, and its whole-program theorem includes those instructions.

The function trampoline is fixed before receiving argument values; it passes variables,
not input-specialized constants. Its count is the actual enclosing call count plus one
halt. In [the runnable factorial example](##Examples.Ram.FunctionRun), argument 5 returns
120 in 218 transitions without a step limit. A typed array argument is still two ordinary
words at this boundary, not an implicit allocated object or a free memory copy.

`Ram.LocalCompiler.Function.runUntil_of_execution` derives the result from the function proof
under code-fit and stack-fit premises, without a time estimate.
`Ram.LocalCompiler.Function.run` additionally offers an operational limit.
Host-side argument and heap preparation is explicit
preloading, not a charged RAM loader; a complete input-loading program needs its own
implementation and count. See the
[function compilation interface](##Complexity.Computability.Ram.Compiler.Local.Function).

## What observations survive compilation?

The source-visible heap lies below a natural boundary `H`; the compiler's private stack
starts at `H`. `Ram.HeapEqBelow` relates the visible heap, while
`Ram.Source.State.Observes` also retains the permitted local-register and I/O observations.

The complete source and target memories need not be equal. Returned stack frames may leave
stale words outside the source heap, and source contracts cannot observe arbitrary compiler
registers. Use the supplied model-observation bridges to transport the actual postcondition.

For a global local-register bound `N`, entry stack pointer `b` and remaining nesting bound `d`,
the usual sufficient stack condition is:

```text
H ≤ b
b + d * (N + 1) < 2^w
```

The strict inequality keeps the exclusive-end stack pointer representable. Target code
addresses must also fit; the whole-program theorem uses `code.length < 2^w`.
These bounds concern addressing and capacity, not whether all program arithmetic is exact.
Word-valued Boolean interpretations additionally require positive word width.

## How calls are charged

The default `Ram.LocalCompiler` uses a callee-sized frame. A call evaluates its arguments
in the caller state, saves the return address and the `l` caller registers its callee can
overwrite, passes the arguments, runs the body, then restores the caller.
Heap and I/O effects remain shared.
All save, initialization and restore work is emitted code; there is no unit-cost bulk copy.

`Ram.ABI.callLocals_steps_eq` gives the count for a call with `p` arguments:

```text
compiled argument lengths + measured body steps + compiled result length
+ 7 * l + p + 11
```

The result expression is evaluated before restoring the caller, and the count includes the
call and return control transfers. Increasing an unrelated function's local bound does not
increase this call's frame work. `Ram.Compiler` retains the global-bound reference compiler.

`Ram.Func.bodyTime` excludes the enclosing call's argument evaluation, frame setup and
return sequence, including evaluation of that function's own return expression. Nested
calls inside its body include their complete generated call code. For example,
[squaredNorm](##Examples.Ram.LocalBindings) has body time 46 from two 23-step calls;
its final addition is in its own return expression and is not part of those 46 steps.

Most users need the proved function contract, not the physical register assignment.
Backend contributors can follow the
[ABI layout](##Complexity.Computability.Ram.Compiler.Local.ABI.Basic),
[call simulation](##Complexity.Computability.Ram.Compiler.Local.Call.Basic) and
[measured execution](##Complexity.Computability.Ram.Compiler.Local.Measured.Basic) modules.

## Which space claims are available?

`Ram.PrefixBound` bounds a state observation at every real execution prefix.
`Ram.HasPeak` also witnesses a prefix attaining the bound. Sequential time counts add;
peaks combine by maximum. See [prefix resources](##Complexity.Computability.Ram.Execution.Resource).

`Ram.heapAccesses` and `Ram.heapWrites` collect actual load/store addresses, including
compiler-stack accesses. They combine by union across an executed cut, and their frame
theorems preserve cells outside the actual writes. Unlike endpoint equality, the prefix
results can rule out temporary writes during a run.

A heap boundary bounds addresses; a visited-address set is a cumulative footprint.
Neither is automatically peak live storage. Saved-frame and partial save/restore lemmas
describe the actual calling protocol, but a complete tight nested-call live-space result
is still missing. In particular, `SP - H` is not enough: setup writes before advancing `SP`,
and return retreats it before restoration finishes. General allocation and reclamation
also need their own semantics before supporting live-heap bounds.

See [execution footprints](##Complexity.Computability.Ram.Execution.Memory),
[saved frames](##Complexity.Computability.Ram.Compiler.Local.ABI.Stack) and
[frame lifetimes](##Complexity.Computability.Ram.Compiler.Local.ABI.Lifetime) for existing results.

## State the size measure and model with the theorem

A uniform complexity claim fixes one program before quantifying over inputs and allowed
word widths. The problem contract chooses encoding, admissible widths and size measure:
number of words, numerical magnitude and binary length are different quantities.
`Ram.wordListBitSize` counts packed word payloads, not an external encoding of the width
or list length.

The library's encoding-size bounds and polynomial-time composition are word-RAM results.
There is currently no proved RAM-to-Turing-machine simulation. A bit-cost or Turing-machine
complexity-class claim needs an explicit encoding and a simulation with justified overhead;
it does not follow just from using the name "polynomial time".
-/
