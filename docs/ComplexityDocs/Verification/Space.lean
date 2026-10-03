/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Space
import Complexity.Program.ParsedSpace
import Complexity.Program.ArrayFunctionSpace
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceAsymptotics
import Complexity.Computability.Ram.Problem.Space
import Complexity.Language.Session.Space

/-!
# Proving space bounds

Space and time describe the same compiled program. State functional correctness
independently, then supply either a finite space budget or an asymptotic bound.

For `solve : Complexity.Program Query Answer`, the public predicates are:

```lean
solve.Correct legal post
solve.TimeO legal size timeGrowth
solve.SpaceO legal size spaceGrowth
```

`SpaceOOn legal target` accepts a possibly multivariate expression directly on
the mathematical input, just as `TimeOOn` does. `SpaceBound legal w budget`
instead fixes a machine width and a concrete word budget for every legal input.
Both forms require an actual successful execution. A capacity or width premise
cannot silently remove difficult inputs from the legal domain.

As with time, a finite legal input family does not distinguish asymptotic
classes. Use a concrete `SpaceBound` for a fixed contest memory budget, or state
an unbounded legal family for a meaningful asymptotic comparison.

## What a word of space means

The observation is the cardinality of a finite address set:

* the input interface's preloaded arena prefix, including its metadata and any
  reserved padding;
* all addresses actually loaded or stored during the complete invocation,
  including compiler-generated call-stack accesses.

Their union counts a physical address once. Reading the same array repeatedly,
reusing a scratch region, and reusing a call frame do not repeatedly charge those
words. The seed belongs to the fixed input interface, not to the candidate.
The observation includes intermediate accesses, not only the final heap.

This is a **physical-word footprint**, not exact peak reachable-live data and
not cumulative allocation. It is also not the largest address used: the arena
and stack may be separated by a large unused address interval. The fixed
`heapLimit` is an address-layout boundary, not an algorithm's space budget.

Code, registers and external input/output streams are outside this heap-word
measure. A preloaded `Program` counts its input arena; the lower-level raw RAM
interface starts with an empty heap seed because its input is a separate stream.
Host-side loaders, decoders, runtime object overhead and process RSS are not
identified with this model's words. Source allocations and output construction
executed by the program do contribute their actual accesses.

At a fixed 64-bit width, a model budget of 512 MiB corresponds to 67,108,864
eight-byte words. This conversion does not assert that a native Lean process
has the same memory consumption. State the chosen I/O and runtime boundary when
using such a budget in a benchmark.

## Correctness, time and space in one execution

`SpaceBound.runs_correct` and `SpaceO.runs_correct` combine an independent
`Program.Correct` proof with a space certificate. Their output representation,
mathematical postcondition and memory observation belong to one execution.
`TimeO.runs_space` combines independent time and space certificates by identifying
the deterministic run at a common admitted width. It does not choose a cheap
time execution and an unrelated small-space execution.

For raw sequence inputs, `SpaceBoundParsed` and `SpaceOParsed` retain the fixed
specification parser and the original raw-input execution. Parsing a mathematical
query does not preload a second decoded object or grant algorithmic advice.
The `ArrayFunction` space predicates are compatibility wrappers through
`toProgram`, not a separate cost model.

## Proving the bound

Bound the actual accessed region, including temporary storage and stack frames.
For separated heap and stack intervals, add their word counts, not the numerical
gap between their addresses. Sequential execution combines address sets by union;
it is not valid to take the maximum of two arbitrary unrelated footprint sizes.
Reuse or containment can justify a stronger bound.

The arithmetic step uses ordinary mathlib `IsBigO`. The tactic
`program_space_asymptotics [leaf, one, ...]` reuses the time interface's arithmetic
composition for sums, maxima and constant factors. Supply the genuine space
envelope first. The tactic neither discovers lifetimes nor proves which addresses
are accessed. A supplied `1 =O growth` fact accounts for constants.

`spaceWords ≤ inputReservation + steps` is available as a general fallback,
but an independent space proof can be much tighter than the running-time bound.
A restored final allocation cursor alone is insufficient: scratch memory used
before reclamation still belongs to the execution's physical footprint.

## From source contracts to the space theorem

`SpaceO.of_measured` and `SpaceO.of_measured_depth` publish an independent space
bound from the existing source execution and its arena readiness. A small heap
envelope and a call-depth envelope describe the accessed regions. The machine
keeps its original stack base, compiled code and input state: a smaller resource
proof must not select a different implementation. The compiler connection
proves that all accesses belong to the small heap region or the separate stack
region. The resulting word bound adds their sizes and omits the address gap.

The `_auto` variants reuse the time interface's code/stack capacity machinery;
they do not infer the algorithm's heap bound, lifetime invariant or depth bound.
Readiness and the input's representation in the smaller arena remain explicit
obligations for all legal inputs, including empty objects and aliases.

The existing [scoped scratch consumer](##Examples.Language.ScopeCompiled) proves
`make_spaceBound`: repeated calls reuse their two scratch regions and call
frames. Its bound is independent of the repetition count and retains the same
mathematical result and final cursor. The
[typed program consumer](##Examples.Language.ProgramCompiled) publishes
`append_spaceO` and `append_time_space_correct` for the existing append program,
including its initial input reservation. These are existing implementations,
not separate mathematical programs substituted for the compiled code.

## Persistent and prepared sessions

Import `Complexity.Language.Session.Space` for the finite and uniform session
interfaces. The ordinary, accepted-trace, scheduled, phase, prepared-history and
prepared-worst-case variants retain their time counterparts' information and
width boundaries. Initialization contributes even to an empty history. Each
callback receives only its current request and the actual retained state.

A session's footprint is an address union across initialization, current-input
preparation and callbacks. Neither the heap nor the space history is reset at
call boundaries. The paired time-and-space predicates use one decorated trace;
for an adaptive protocol, separate existentially accepted traces cannot simply
be combined as if they had selected the same interaction.

The interface author fixes preparation before a candidate is selected. The
concrete buffer and list preparation-space modules observe their real allocating
and writing calls and erase back to the existing preparation relation. A user
annotation asserting that an arbitrary loader uses no space is not such a proof.
Grader/oracle work and external transport remain outside the contestant trace.
-/
