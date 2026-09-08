/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Execution backend

The RAM backend supplies the execution and counting semantics beneath the reusable
verification interfaces. This chapter documents its assumptions and compiler boundary.
Most client proofs should apply operation, function and model contracts rather than repeat
the protocol below.

## Machine model

The machine is a parameterized unit-cost word-RAM with a fixed finite instruction vocabulary.
A word is `BitVec w`. Arithmetic, addresses and comparisons retain their bit-vector semantics;
natural-number interpretations require proved range conditions. Each successful transition
costs one, including multiplication and division. This is a word-RAM choice, not a claim that
unbounded integer multiplication has constant bit cost.

`Ram.Exec` is the exact transition relation. `Ram.TerminatesWithin` includes a real execution
and a halted endpoint. Faults, invalid control flow and exhausted input are not successful
termination. The executable bounded runner agrees with the reference semantics, and the
optimized array/register and sparse-memory representation is connected by `Ram.Fast.map_run`.
Host execution time is not the formal cost model.

One compiled program is fixed before quantifying over input sizes and admissible word widths.
The problem specifies encoding, allowed widths and size: numerical magnitude, number of
words and binary length are different measures. `Ram.wordListBitSize` counts packed word
payloads, including actual input headers, not an external encoding of the width or length.
Its polynomial bound is a representation-size theorem, not a bit-machine simulation.

The current backend does not establish RAM-to-Turing-machine simulation or automatic
membership in a Turing-machine class such as P. Such claims need an explicit finite-alphabet
encoding, width policy and proved simulation overhead.

## Source and checked compilation

Source expressions and statements use fixed constructors, not arbitrary Lean callbacks.
Proofs, invariants, mathematical models and potentials are ghost data; they cannot provide
runtime computations or custom instruction prices.

`Ram.LocalCompiler.compileChecked` checks register bounds, function lookup and arity, then
emits finite code. `Ram.Source.SafeExec` records source execution with justified accesses,
successful reads and sufficient call depth. `Ram.Source.LocalMeasuredExec` attaches the
count derived from the emitted instructions. Its simulation covers structured control flow
and recursive calls using finite execution derivations, not an acyclic call graph.

`Ram.LocalCompiler.compileChecked_runs_measured` connects this to the complete target run,
including the actual heap-boundary input read and final halt. Code-address fit, safe heap
accesses and sufficient stack capacity are proof premises; checked compilation does not
insert a runtime bounds check for every access.

The default compiler is callee-sized: a call saves and restores only the local-register
interval its callee can overwrite. An unrelated function with many locals does not inflate
that call's execution count. The global-bound `Ram.Compiler` remains an explicit reference
implementation rather than the public default.

## Observation boundary

Let `H` be the source-visible heap boundary and `k` the active function's local bound.
`Ram.HeapEqBelow H source.mem target.mem` relates memory below `H`.
`Ram.Source.State.Matches H k source target` additionally relates active local registers,
input, output and running status.

Do not substitute equality of the entire source and target heaps: the target contains a
private call stack, and returned frames may leave stale words there. Nor does a source
contract justify arbitrary observations of registers outside its declared bound.
`Source.State.Observes` and the model-specific observation lemmas transport exactly the
visible postconditions after compilation.

For a preloaded algorithm, the block-entry theorem requires an explicit matching initial
memory state. It counts the ensuing block and halt, not unspecified preprocessing.
An initial-machine certificate separately supplies the actual encoding and representation.

## Register and frame layout

For a fixed linked program choose `N` bounding every declared local interval, with each
function satisfying `params ≤ locals ≤ N`. All function bodies appear once in the code;
recursion reuses that code and register layout.

| Physical registers | Meaning |
| --- | --- |
| `0, …, N - 1` | Source local registers |
| `N` | Stack pointer `SP` |
| `N + 1` | Return value `RV` |
| `N + 2` | Return address `RA` |
| `N + 3`, `N + 4` | Address and offset temporaries |
| `N + 5 + i`, for `i < N` | Evaluated argument buffer |
| `2 * N + 5` and above | Expression temporaries |

The expression compiler preserves registers below its scratch bound and all memory.
Source locals therefore remain in their original physical registers while argument
evaluation uses disjoint temporaries and buffers.

If the callee declares `l` locals and call-entry SP is `b`, its frame has `F = l + 1` words:

```text
b             saved return address
b + 1 + i     previous caller register i, for i < l
b + F         next free stack address after setup
```

The stack grows upward from `H`. The simulation also preserves registers between the
active callee's local bound and `N`; they may contain live values of an older caller.

## Call and return protocol

For a fixed call with `p` arguments and a callee with `l` locals:

1. Evaluate all arguments in caller state and buffer their values. Each evaluation preserves
   already buffered arguments and source locals.
2. Store the return code address at SP, then save registers `0, …, l - 1` in the following
   frame slots. Each address calculation and store is emitted machine code.
3. Copy arguments into the callee parameters and zero-initialize its remaining locals.
4. Advance SP by `l + 1` and jump to the linked function entry.
5. Execute the body, then evaluate the result expression in the final callee state.
6. Buffer the result in RV, retreat SP, load RA and restore the saved caller locals.
7. Jump through RA and move RV into the caller's destination register.

The result is evaluated before restoration. Heap and I/O effects remain shared; the callee's
other locals do not survive return as caller observations. Setup and return are finite
instruction lists, not primitive whole-frame copies. No instruction runs an arbitrary Lean
function supplied by a proof.

For these actual sequences, `Ram.ABI.callLocals_steps_eq` derives:

```text
sum of compiled argument lengths
+ actual compiled body steps
+ compiled result length
+ 7 * l + p + 11
```

This is a theorem about generated code and its execution, not a separately chosen price.
`LocalCompiler.simulate_call_exact` includes entry and return jumps and the receive move.
Changing emitted code requires changing its execution and length proofs as well.

For implementation details, see `Complexity.Computability.Ram.Compiler.Local.ABI.Basic`, `Complexity.Computability.Ram.Compiler.Local.Call.Setup`, `Complexity.Computability.Ram.Compiler.Local.Call.Return`,
`Complexity.Computability.Ram.Compiler.Local.Call.Basic`, `Complexity.Computability.Ram.Compiler.Local.Measured.Basic` and `Complexity.Computability.Ram.Compiler.Local.Program.Basic`.

## Safety and capacity

Every source expression read must stay below `H`; a store's destination must also be below
`H`. Call arguments are checked in the original caller state and the result expression in
the final callee state. A successful input read requires available input.

With natural entry SP `b`, remaining nested-call allowance `d` and width `w`, the standard
sufficient stack condition is:

```text
0 < w
H ≤ b
b + d * (N + 1) < 2^w
```

The strict inequality keeps the exclusive-end SP representable as a word. Actual calls use
their own `l + 1 ≤ N + 1` frames. Code addresses also need to fit; `code.length < 2^w` is a
sufficient condition used with resolved label membership. None of these capacity conditions
prohibits ordinary modular arithmetic on program values.

The heap boundary is a sufficient maximum-address requirement, not peak occupied storage.
The depth-times-maximum-frame expression is conservative. Tighter actual resource claims
use observations of the execution itself.

## Resource observations

`Ram.PrefixBound` bounds an observation at every real execution prefix, including both
endpoints. `Ram.HasPeak` also supplies an attaining prefix. Sequential transition counts
add; attained resource peaks combine by maximum. An observation of a sum at each state is
different from the sum of separately attained peaks.

`Ram.heapAccesses` and `Ram.heapWrites` are finite sets of actual load/store addresses,
including compiler stack accesses. They exclude registers, instruction fetches and separate
I/O streams. At a real execution cut, the footprint sets combine by union. An instruction
present at the endpoint but not executed is not counted.

`Exec.mem_eq_of_not_written` preserves cells outside actual writes; the prefix variant
preserves them throughout the run. The array and source-heap corollaries retain their
representations at each prefix. Endpoint equality alone cannot establish absence of temporary
writes. Distinct visited-address counts are bounded by executed steps, but remain cumulative
footprints rather than peak live space.

For linear blocks, `Exec.eq_execBlock_take` identifies every actual prefix with the appropriate
instruction-list prefix. Access characterization evaluates each instruction in its own entry
state. Expression compilation has no heap writes, while its load bound includes reads used
to compute another address. Atomic-store footprints include both operand evaluations and
the final store. Argument evaluation and local initialization have no writes.

Complete recursive simulation in `Complexity.Computability.Ram.Compiler.Local.Measured.Memory` bounds accesses using the real
entry SP and remaining nesting envelope. `Complexity.Computability.Ram.Compiler.Local.Measured.Writes` separates source-heap
writes from writes at or above entry SP, preserving older frames in between throughout
nested execution. Complete initialization yields the bound
`H + depth * frameSize control`; the actual header read and halt add time but no heap access.

## Saved-frame lifecycle

`Ram.ABI.frameSlots` identifies a frame's actual address set, and its cardinality and
disjointness lemmas use ordinary finite sets. No-wrap conditions connect word sets to natural
intervals. A set's exclusive endpoint may equal `2^w`, while an advanced SP still requires
the compiler's stricter representability premise.

The frame-prefix interfaces distinguish completed stores and restores. After `k` transitions
of the local-save or local-restore list, the completed slot indices are below `k / 3`; the
other two instructions for each slot calculate its address. `pendingLocalSlots` describes
precisely the remaining restore obligations and their count.

`SavedFrames` records an ordered newest-first list of saved return words and local values
in one memory. Its slot cardinality is the ordinary sum of frame sizes. Call setup extends
this list; recursive prefix theorems preserve older saved values. Return-prefix theorems
combine restored caller registers, the retained older frames and precisely pending locals
at the same actual endpoint.

These lemmas are in `Complexity.Computability.Ram.Compiler.Local.ABI.Slots`, `Complexity.Computability.Ram.Compiler.Local.ABI.Lifetime`, `Complexity.Computability.Ram.Compiler.Local.ABI.Stack` and
`Complexity.Computability.Ram.Compiler.Local.Exact.Stack`. They describe the real protocol's obligations, not a heap allocator
or a complete tight live-space theorem. In particular, instantaneous `SP - H` is insufficient:
setup saves before advancing SP, and return retreats SP before restoring. A tight complete-run
space result still needs a representation of outstanding frames across every recursive phase.

## Execution measurements

The existing `ram-demo` driver compares fast and reference execution of the same write-then-sum
program. Timing includes creating the initial machine state but excludes compilation and
executable preparation. A non-inlined IO boundary keeps the measured execution inside the
timer interval.

Run the workload with `lake exe ram-demo fast 1000`, `lake exe ram-demo reference 1000` and
`lake exe ram-demo fast 100000`. Compare the reported transition count, stopping reason and
output before interpreting timing differences. Measurements from one host and workload
are not portable speedup guarantees. The formal equality between backends concerns decoded
execution results, not equal host runtimes.
-/
