/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Functional verification

Functional correctness should describe what a program computes without requiring a proposed
instruction bound. Time analysis can then reuse its invariants and observations independently.
The implementation-to-model connection remains a theorem, not an assumption introduced by a tactic.

## Total contracts and specifications

`Ram.Source.TotalContract` proves safe terminating execution from a precondition to a
postcondition. `Ram.Source.TotalRelContract` also lets the postcondition refer to the entry
state. Neither contains a time budget. Heap capacity and permitted call depth are safety
parameters: they justify the implementation's memory accesses and call stack, not its runtime.

`Ram.Source.Refines` connects one fixed source statement to an ordinary Lean function
through input and output representation predicates. Its form is:

```lean
Refines program heapLimit depth stmt inputRep outputRep f
```

For every mathematical input `x`, represented concrete inputs terminate in a state
representing `f x`. The representation may include safety, encoding and frame facts.
`Ram.Source.Refines.spec` transfers an ordinary theorem about `f` to the actual result.
`Ram.Source.Refines.seq` composes implementations through the shared mathematical model;
the second program is executed on the real intermediate state.

The following proof is taken from `Examples.Ram.Verification`. There, `main` reads a word,
increments it, and writes the result; `increment` is its source addition expression:

```lean
theorem main_refines (rest out : List (Word w)) :
    Refines [] 0 0 main
      (fun x s => s.input = x :: rest ∧ s.outputRev = out)
      (fun y t => t.input = rest ∧ t.outputRev = y :: out)
      (fun x : Word w => x + 1) := by
  ram_refine x s ⟨hin, hout⟩ [main, increment, hin, hout]
```

It describes modular word addition and retains the unconsumed input and previous output.
No instruction budget appears in this correctness proof. The same module proves
`main_timeBound` separately and combines them with `with_timeBound` before exporting the
complete halted execution.

## Proof workflow

1. Choose the ordinary mathematical object and the intended property. Reuse Lean, Std and
   mathlib definitions and theorems where they fit.
2. Reuse an existing implementation refinement, or establish its representation relation
   with `ram_refine x s hs [facts]` or `ram_total_vc s hs [facts]`.
3. Apply proved operations and function specifications with `ram_total_apply`. Keep their
   implementations opaque at the use site.
4. Prove loop invariants and recursion progress in ordinary Lean. Supply the implementation's
   guard, body and safety connections at their respective boundaries.
5. Transfer the mathematical property through `Refines.spec`, or retain it for further
   composition with `with_postcondition`.
6. Prove time separately and export the same result to the compiled execution.

A costed contract's `.total` projection remains available for existing results, but it is
not an independent correctness proof. New functional developments should use the total
interfaces directly when the necessary implementation lemmas are available.

## Optional native stateful models

An ordinary `StateM σ α` computation maps an initial mathematical state to a returned value
and final state. It is useful for specifications involving several updates, but is optional:
pure functions and direct contracts are equally valid interfaces. Users should reuse supplied
models and refinements, rather than reproduce a second version of every program.

The native proof interface is Lean's `Std.Do.Triple`; `import Std.Tactic.Do` supplies `mvcgen`.
For example, `Examples.Ram.Verification` contains:

```lean
def incrementState : StateM (Word w) PUnit := do
  let value ← get
  set (value + 1)

open Std.Do in
theorem incrementState_spec (x : Word w) :
    ⦃fun state => ⌜state = x⌝⦄ incrementState
    ⦃⇓ _ state => ⌜state = x + 1⌝⦄ := by
  mvcgen [incrementState]
  simp_all
```

`Ram.Source.Refines.stateM_spec` transfers such a triple through a proved implementation
refinement of `model.run`. `stateM_spec_refines` retains the native postcondition alongside
the output representation, so subsequent operations can use it without reconstructing an
execution witness. The pure counterpart is `with_postcondition`.

`stateM_bind` composes both the returned value and state using native bind. Its second
mathematical computation may depend on the returned value, but the second source statement
is fixed: its representation explains how runtime registers or memory supply that value.
It does not generate executable syntax from a proof-only input.

Native `mvcgen` proves the mathematical computation. It does not compile arbitrary Lean
code, infer the representation, or prove RAM overflow, heap or stack safety. The pinned Lean
version labels `mvcgen` experimental; the transfer uses its standard verified triple semantics.

## Control flow and recursion

`Ram.Source.Refines.ite` relates an actual source guard to an ordinary predicate. Each branch
requires a refinement only on its reachable mathematical domain. `while_wellFounded` uses
an abstract state, invariant, continuation predicate, step and result function. Preservation,
well-founded progress and the equation saying a step preserves the eventual result are
ordinary Lean propositions. Guard/body representation and endpoint observations connect them
to source execution.

`TotalWP.while_variant` is the direct functional rule for a decreasing natural variant.
For a native traversal, `Refines.stateM_forM` connects `List.forM xs action` to one fixed RAM
while. A representation of the remaining visits and current mathematical state relates the
guard to nonemptiness and each real body step to `action head`. It handles a fixed finite
traversal, not early returns or dynamically growing worklists.

Recursive specifications use `Ram.Source.Recursion.TotalSpec`. Its well-founded verification
rule supplies correct smaller calls without unfolding their bodies or adding time bounds.
`Correct.wp_call` and `ram_total_apply` reuse these calls. Natural measures, lexicographic
orders and other existing Lean well-founded relations are suitable.

`Refines.call` packages a function specification as a refinement of a fixed call statement.
Argument binding, return adaptation and the function's lookup/arity facts are established at
that boundary. `Refines.stateM_call` provides the analogous bridge from a native stateful
body without requiring another specification record. Shared heap and I/O effects survive
return; caller locals other than the destination are restored by the call theorem.

For low-level adapters, `State.enter_regs_getElem` exposes standard parameter indexing,
and `State.leave_eq_setReg_of_frame` simplifies a return when heap and I/O preservation have
actually been proved. These are implementation lemmas, not facts each mathematical client
should have to reproduce.

## Changing and combining models

Use `Refines.congr_fun` for an equality of mathematical functions. `equiv` changes genuinely
equivalent models using ordinary mathlib equivalences. `transfer` uses `Relator.LiftFun` for
related or lossy models: representatives must exist and the computation must respect the
chosen relations. A set observation cannot automatically replace a multiset computation.

`map_output` changes the output observation; `comap_input` reparameterizes represented
inputs. `TotalContract.and`, `TotalRelContract.and` and `Refines.prod` combine independent
facts about the same statement. Determinism identifies the final state: these are not parallel
runs or claims of disjoint memory. Ghost witnesses can be moved with `TotalWP.exists_iff`.
The universal form requires a nonempty index type, because an empty family cannot witness
termination.

For product states, changed subviews and unrelated heap objects, see
[data models and memory](##ComplexityDocs.Models).

## Focused automation

| Tactic | Purpose |
| --- | --- |
| `ram_total_vc s hs [facts]` | Generate budget-free verification conditions |
| `ram_refine x s hs [facts]` | Start a refinement for a represented mathematical input |
| `ram_total_apply h` | Apply a supplied functional contract or call specification |
| `ram_model [facts]` | Rewrite model observations using ordinary simplification and word facts |
| `ram_word [facts]` | Normalize unsigned word arithmetic with justified range conditions |
| `ram_bound [facts]` | Normalize proved instruction bounds and arithmetic obligations |

The introduction forms accept ordinary patterns, including `⟨hmodel, hbounds⟩` and ghost
witnesses. `ram_model`, `ram_word` and `ram_bound` accept simplifier locations such as
`at h`, `at h ⊢` and `at *`. Model simplification reuses the native `StateT.run_*` rules and
the identity-monad definition so returned state observations can simplify normally.

Representation equations and mathematical facts must be supplied or registered with Lean's
ordinary `simp` mechanism. There is no separate model registry. Program bodies, unknown
invariants and supplied contracts remain opaque unless explicitly unfolded. Residual goals
are ordinary Lean goals for `simp`, `omega`, `ring`, `grind` or other appropriate tactics.

Word normalization uses proved no-wrap facts when available, otherwise it retains modular
semantics. It does not invent ordering assumptions for subtraction or natural interpretations
of overflowing multiplication. Signed, bitwise and nonlinear reasoning may need additional
mathlib facts. None of these tactics synthesizes algorithmic invariants or infers a Big-O claim.
-/
