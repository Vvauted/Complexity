/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Ram.FunctionComposition

/-!
# Direct word-RAM proof automation and composition

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Automate the routine work

`ram_refine x s hs [facts]` starts a refinement proof;
`ram_total_vc s pattern [facts]` starts a state-based total-contract proof;
`ram_total_vc args entry pattern [facts]` starts a `FunctionContract` directly.
Precondition patterns include `rfl` and `⟨rfl, hbound⟩`. Closed frame bounds may
be discharged automatically; unresolved obligations remain ordinary Lean goals.
Use `ram_total_apply contract [facts]` to apply a supplied operation, function or
recursive specification while keeping its implementation opaque. The dedicated
`ram_bindings` set supplies declaration-generated argument fields, lookups and
static parameter/result/local counts, including imported functions. Authors
still choose the contract and typed input, but need not repeat caller/callee
argument-builder definitions. Bodies, return expressions and mathematical
representation lemmas are not registered in this set.

For a named function whose initialization needs mathematical reasoning, use
`ram_total_start args entry pattern` to apply the existing function rule without
advancing the body. Then

```lean
ram_total_init functions.function.lowerBound at initial with bindings
```

follows the actual leading assignment statements, stopping before calls or
control flow. `initial` names the current source state. The visible locals
become ordinary Lean values such as `initial.xs : ArrayRef w` and
`initial.lo : Word w`; `bindings.xs.base`, `bindings.xs.length` and `bindings.lo`
relate these values to their actual source bindings. Nested locals such as the
search midpoint are not visible before entering their scope. An array local is
exposed only after its two field assignments have both executed.

The [named search proof](##Complexity.Computability.Ram.Array.Search.Function)
uses these facts with `Search.Pre.invariant`, then applies its existing loop
contract. It does not write a separate `State.enter`/`setReg` initializer.
The independent time proof uses `ram_time_start` and `ram_time_init` with the
same syntax, but applies the existing conditional time rules and charges the
actual assignments. Both initialization forms accept optional `[facts]`;
unsolved safety or affordability goals remain explicit. Neither form invents a
loop invariant or advances through a call.

To enter the next source conditional, select its branch explicitly:

```text
ram_total_branch f then at current with bindings [facts]
ram_total_branch f else at current with bindings [facts]
ram_time_branch f then at current with bindings [facts]
ram_time_branch f else at current with bindings [facts]
```

`then` requires the actual guard to be nonzero; `else` requires it to be zero.
Selecting a branch does not assume that condition: unresolved guard, read-safety
or time-affordability obligations remain ordinary goals. The step enters that
branch's lexical scope and advances its leading initializers, stopping before
another conditional, call, loop or other effect. Statements following the
conditional are retained; an omitted `else` executes the actual empty branch.

The [recursive sort implementation](##Complexity.Computability.Ram.Array.MergeSort.Function)
starts its large-input case with `ram_total_start`, followed by
`ram_total_branch sortFunctions.function.sort then at initial with bindings`.
Supplied range facts prove the guard. The actual source declarations then produce
`initial.middle : Word w` and `initial.left`, `initial.right : ArrayRef w`.
Both descriptor assignments complete before an array local becomes visible.
These values are passed to the existing recursive and merge contracts; no raw
slots or separately reconstructed initializer state are needed. Halving,
slice containment, disjointness and changed-heap reassembly are still proved
with the existing mathematical lemmas.

The [separate time proof](##Complexity.Computability.Ram.Array.MergeSort.FunctionTime)
uses `ram_time_start` and the corresponding `ram_time_branch`. Its rules retain
the actual guard evaluation, branch jumps and field-assignment costs; they bound
completed executions without using the initialization's total-correctness proof.
The proof starts from the original whole-body bound, with no hand-selected
intermediate branch reserve. The recurrence and proof that the complete work
fits that bound remain explicit, while remaining allowances follow from the
actual operations.

Without a cursor, these entry points require the named function's whole body.
An initialization or branch step records its exact lexical block and next child
only on the remaining code goal, so another such step can continue there.
The actual code is rechecked at that fixed position: no search for an equal AST
or re-elaboration of embedded source terms is used. This does not locate an
arbitrary prefix after unrelated proof tactics have advanced it.

The generated Lean lets are snapshots at the named state, not live readers of
later registers or heap contents. They remain usable in ordinary call proofs;
sort's `Unit` calls restore the caller locals containing its descriptors.
Representations of changed arrays still require the actual callee postcondition.
Ordinary call tactics do not advance the source cursor or automatically bind a
new source-local result name. Entering loaded loop-body scopes and elaborating
source-level invariants remain unfinished. See
[source-directed initialization and branches](##Complexity.Tactic.Ram.Source).

For a typed function call, `ram_total_apply contract on input [facts]` selects
the actual mathematical input and passes the returned value and shared effects
to a continuation with caller locals restored. It only attempts to close the
lookup, result-count, argument-read and argument-value obligations completely,
using declaration equations and locally generated source-binding facts.
The functional precondition, call-depth condition and continuation retain their
original form. In particular, supplying a slice definition to match runtime
arguments does not also expand every represented slice in the continuation.
Merge sort uses this form for both recursive calls, merge and copy-back.

Use `ram_total_store represented at index := value [facts]` to write one element
of a represented array. It applies the existing array-store contract to the
actual `TotalWP` store, opening one leading sequence when needed. No address
expression, value expression or destination register needs to be repeated.
The continuation retains the real updated state, a representation of
`contents.set index value`, and the outside-array frame. The
[map implementation](##Complexity.Computability.Ram.Array.Map.Correctness) uses:

```lean
ram_total_store h.array at i := (transform xs[i])
  [indexFits, h.base_eq, h.index, arrayAddr]
```

Only completely solved side conditions are discharged. Index bounds, current
representation, read safety and address/value equations otherwise remain visible;
the continuation is not simplified. A representation survives local-register
changes by its definition, but cannot be reused across a genuinely changed heap
without a proof. The tactic neither advances the next statement nor supplies
the next invariant. See [array automation](##Complexity.Tactic.Ram.Array).

Use `ram_total_bind mid hmid [definitions, facts]` on a `TotalWP` assignment
or a sequence beginning with one to name that assignment's actual word value.
The continuation receives `mid` and `hmid : mid = entry.eval expression` without
expanding the value or advancing later statements. The optional list unfolds
only the supplied definitions before applying the rule. Read safety is closed
only when `ram_simp` proves it; otherwise it remains a separate goal.
The [search body proof](##Complexity.Computability.Ram.Array.Search.Total) uses
this to reason about one named midpoint in both branches. The name is local to
the proof continuation, not an exported loop variable; array-result binding,
layout inference and invariant inference are not supplied by this tactic.

`ram_model [facts]` simplifies observations, and `ram_word [facts]` normalizes word arithmetic
with the available range conditions. Remaining obligations are ordinary Lean goals.

Supply representation equations and mathematical facts through these tactic arguments or
Lean's usual `simp` mechanism. The tactics do not infer loop invariants, invent no-overflow
hypotheses or turn modular arithmetic into exact arithmetic. Their API is under
[total verification](##Complexity.Tactic.Ram.Total) and
[model simplification](##Complexity.Tactic.Ram.Model).

## Reuse contracts for included functions

The [source-composition sample](##Examples.Ram.FunctionComposition) includes the
existing copy and sum declarations as `Copy` and `Sum`, then calls them inside one
new function. `functions.importMap.Copy` gives the old-to-new function index map;
`functions.embeds.Copy` proves that the relocated implementation belongs to the
combined table. The [function-linking rule](##Complexity.Computability.Ram.Source.Function.Linking)
`Ram.Source.FunctionContract.renameCalls` transports the original contract through
this embedding, retaining its arguments, returned value and shared-state postcondition.

The public `Ram.Source.Array.copy_function_typed_contract_of_ref` accepts a proof-level
pair of array references, encoding the same source pointer, destination pointer
and source length. Its destination length follows from represented input and
the equal-length premise, not a fourth runtime argument. The result is `Unit`. The sample
relocates this contract and applies its `wp_call_restored` rule with
`ram_total_apply`; declaration-generated bindings supply the lookup facts.
Copy's postcondition supplies both complete `ArrayRef.Rep` assertions, including the one needed by sum,
whose contract is reused through `functions.embeds.Sum`. The standalone
`call Copy.copy(...);` has an empty result list and no dummy destination.
Its postcondition and shared-memory effects still reach the continuation through
the same call rule. This differs from discarding a word or array result, whose
fields are still evaluated and received into private destinations.
Relocation does not discharge representation, equal-length or
disjointness premises. The proof composes the existing contracts without expanding
either callee loop; the generated `applyState` result belongs to one compiled run,
unlike the host-level sequencing in `ArrayCopyFunction`.
Merge sort's final copy uses this same reference contract. The raw and word-triple
typed contracts remain available; neither source signature nor execution cost changes.

The same sample's `imported_sumPair_eval` transports the existing two-array execution
through `functions.embeds.Sum` to `functions.eval.Sum.sumPair`. This also exercises
relocation of the imported function's own two calls to sum, without reopening them
or their loops. Imported aliases export lookup, argument and all six observation/run
interfaces; body equations and local-register names remain with the original declaration.
Generated `params_eq` and `locals_eq` equations are also available under imported
aliases. They expose calling-convention sizes without unfolding the callee body.
The separate time proof reuses the same functional postcondition: `ram_time_apply`
with `on input` passes copy's destination representation through restored caller
bindings and derives the remaining sum-call reserve from the overall body bound.
The proof still establishes that the complete copy call fits; neither a register
equality nor a hand-selected intermediate reserve is needed. The bound belongs
only to the time proof, not the correctness contract or executable call.
See [proving complexity](ComplexityDocs/Complexity.html).

## Publish and link a verified implementation

Use `Ram.TotalComponent.ofNamed` to package a fixed named program with its
`Ram.Source.TotalContract`, shared input/output representations and safety capacities.
There is no time-bound field. `Ram.TotalComponent.comp` links independent function tables
and composes their total correctness on the actual intermediate representation.

Heap and call-depth capacities are still required for safety, and the output-size guarantee
supports later composition. These are not proposed instruction budgets.
`Ram.TotalComponent.runs_observed` exports an actual halted execution before time analysis.
See [budget-free components](##Complexity.Computability.Ram.Component.Total).

## Attach time and export the result

`Ram.Source.TimeBound` bounds completed measured executions; alone, it does not prove that
one exists. Combine it with the correctness proof using
`Ram.Source.TotalContract.with_timeBound` or `Ram.Source.Refines.with_timeBound`.
The resulting contract bounds the same safe terminating execution.

If a continuation has a uniform bound at every intermediate state,
`Ram.Source.TimeBound.seq_const` adds its bound to the first command's bound
without requesting a functional contract. Map uses this for its actual
store/assignment tail. State-dependent continuation bounds still need the
relevant intermediate facts; the uniform rule does not establish them.

For a reusable program, establish a scalar, input-size-based time envelope through
`Ram.TotalComponent.TimeBoundOn`, then use `Ram.TotalComponent.withTimeBound` to obtain
a resource-aware `Ram.Component`. A bound depending on the full input can first be
majorized by such an envelope.
The generated code and non-time guarantees are unchanged; existing component certificates
and polynomial-time interfaces remain available.

Correctness can also be exported without a time estimate.
`Ram.Source.Refines.compile_observed` transports represented outputs to an actual halted
target execution; `Ram.Source.Refines.compile_observed_with_timeBound` adds the separate
time bound. Code fit, stack capacity and output-observation transport are explicit premises.
The [backend chapter](ComplexityDocs/Backend.html) explains these premises and the extra
instructions counted at the whole-program boundary.
-/
