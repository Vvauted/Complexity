# ram-lean

A Lean 4 library for structured imperative programs whose functional correctness,
termination, and running time are tied to a fixed word-RAM execution semantics.

This repository is under construction. It does **not** yet provide the complete
verified language described below.

## Intended contract

A submission is one finite program, uniform across input sizes and admissible
word widths. A successful certificate proves that this program terminates with
an output satisfying the mathematical specification, within a stated number of
RAM transitions. Source-level costs are derived from compiled machine execution;
there is no user `tick` primitive or arbitrary host-language computation escape.

The intended language includes expressions, named local variables, mutable
arrays, structured control flow, ordinary function calls, and recursion. Its
proof layer supplies compositional contracts, loop invariants, termination and
cost reasoning, and arithmetic/memory refinement lemmas.

## Environment

Lean is pinned to **4.28.0-rc1**, matching the existing evaluation/search baseline.
The initial kernel uses Lean/Std only; introducing a newer CSLib or mathlib must
not silently change this baseline.

Compilation takes place on 0v0, in `/home/vvauted/ram-lean`, not on the user's
local computer. A normal checkout builds with `lake build` under the pinned Lean.

See [the design contract](docs/DESIGN.md),
[literature and architectural choices](docs/LITERATURE.md), and
[progress](docs/PROGRESS.md).
