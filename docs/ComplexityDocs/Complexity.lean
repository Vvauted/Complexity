/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity

/-!
# Complexity proofs

The library counts actual execution of a fixed program. Mathematical analysis of those
counts can use ordinary functions, sums, potentials, recurrences and mathlib asymptotics
without repeating machine simulation. The connection between an implementation and its
count remains proved by the compiler and operation contracts.

## Separate behavior and time

`Ram.Source.TimeBound` bounds every completed measured execution satisfying its precondition.
It does not assert that an execution exists. Pair it with independently proved total
correctness using `TotalContract.with_timeBound` or `TotalRelContract.with_timeBound`.
`contract_iff_total_and_timeBound` states the equivalence with the combined contract.

The direction of reuse matters: functional invariants and progress facts may help prove
time, but functional correctness need not depend on a proposed time bound. For recursive
functions, `TotalSpec.withBudget` and `Correct.with_timeBound` attach a count after the
functional specification has been established.

`TimeBound.seq`, `ite`, `call` and `while_potential` compose measured bounds without
threading unused fuel through the functional postcondition. `TimeBound.change_capacity`
reuses an actual count at different heap/depth capacities after totality at the original
capacity rules out a vacuous premise. Its conclusion remains conditional: it does not
assert that the new capacities suffice for termination.

This separation takes inspiration from CALF's distinction between behavior and cost. The
library is ordinary Lean and does not implement CALF's modalities or claim its internal
noninterference theorem.

## Loop analysis

For a loop, write `G` for compiled guard plus conditional-branch work and `B` for the body
bound. The back edge contributes another step. With initial decreasing natural variant `v`,
the linear rule derives:

```text
v * (G + B + 1) + G
```

`TimeBound.while_linear` takes the budget-free body relation and its separate time bound;
invariant preservation and strict decrease are reused rather than mixed into a functional
budget proof. The final false guard is included, including for zero iterations.

Other reusable rules cover common iteration patterns:

- `while_sum` permits body bounds depending on the variant, with skipped values and no
  monotonicity requirement. It uses ordinary finite sums.
- `while_div` uses `Nat.clog b (measure + 1)` when a positive measure decreases to at most its
  old value divided by `b > 1`.
- `while_list` follows an invariant indexed by an occurrence list; each actual body advances
  from its head to its tail. Repeated values count as repeated work.
- `while_list_sum` exposes a tail-independent bound as
  `(visits.map B).sum + visits.length * (G + 1) + G`.
- `while_worklist` allows newly generated tasks; a proved remaining-work measure pays for
  the real body, control flow and future work. It is not restricted to decreasing list length.

These are rules about implemented loops, not free iterators or automatic invariant inference.
Physical traversal, queue manipulation and address computation must belong to the body.

## Amortization

`Ram.Source.AmortizedContract` proves an inequality about an actual execution:

```text
actualSteps + potential(final) ≤ charge(entry) + potential(entry)
```

Sequential composition cancels the intermediate potential and evaluates later charges at
the actual intermediate state. Its `toContract` includes initial credit; it does not assume
that a preexisting data structure was constructed for free.

`potential_consequence` changes potentials after a cross-added endpoint inequality is
proved. Pointwise ordering of two potentials alone is insufficient. `add_potential` covers
the growth of a second potential with an extra charge; `add_nonincreasing_potential` is the
zero-extra-charge case.

Amortized linear, sum and occurrence-list loop rules retain final credit for subsequent
composition. `while_worklist_spawn` permits generated tasks and `List.Perm` reordering,
using occurrence weights and a state-dependent reserve to pay for their creation. Repeated
tasks remain charged. `compile_observed` exports the same final potential and actual target
count, including the real entry and halt overhead.

For pure arithmetic on a finite history, `Finset.sum_range_add_potential_le` derives:

```text
(∑ i < n, cost i) + potential n ≤ (∑ i < n, charge i) + potential 0
```

from the corresponding one-step inequalities. The constant-charge corollary gives
`(∑ i < n, cost i) ≤ n * charge + potential 0`. Empty histories and nonmonotone potentials
are included. General telescoping and traversal counting reuse mathlib's
`Finset.sum_range_by_parts`, `Finset.card_sigma` and `List.length_flatMap`.

## Sums and asymptotics

The asymptotic layer uses mathlib's actual `Asymptotics.IsBigO`; there is no parallel Big-O
definition requiring a separate equivalence proof. `Asymptotics.IsPolynomiallyBounded f` asserts
the existence of a natural exponent bounding `f` by `(n + 1)^k` in that relation.
Its closure rules cover addition, multiplication, powers, composition, maximum and uniformly
bounded finite sums. `exists_pos` obtains an all-input natural bound while covering the
finite prefix below an asymptotic threshold.

Moving sums need uniform bounds. `Asymptotics.isBigO_sum_of_uniform` takes one coefficient and
one eventual condition covering all selected terms in an input-dependent finite set.
`isBigO_sum_card_mul_of_uniform` yields a cardinality-times-majorant bound. The list forms
retain repeated visits without a decidable-equality or no-duplicates requirement.
`Traversal.budget_isBigO_of_uniform` additionally accounts for traversal control flow and
fixed setup: its growth includes the visit majorants and `visits.length + 1`.

Separate per-index Big-O statements are insufficient if their constants or thresholds can
grow with the index. Likewise, a deduplicated union can undercount a nested traversal;
count index pairs or occurrence lists when that is what the program visits.

Discrete logarithms use mathlib conventions. `Nat.clog_two_succ_eq_size` connects
`Nat.clog 2 (n + 1)` to significant-bit length, including zero. `Word.clog_toNat_succ_le`
connects decoded-word length to width. `UniformTimeBound.logarithmic` turns a proved
all-input ceiling-log bound into uniform `O(log2 n)`. It does not turn word-RAM time into
bit-level machine time.

## Recurrences

`Recurrence` analyzes already justified numerical bounds. A recurrence must include
the implementation's recursive calls and nonrecursive work; the arithmetic theorem does
not supply that execution argument.

The successor rules accumulate variable tolls with ordinary sums. `le_of_div_le` compares a
dividing recurrence against a supplied supersolution. For one branch, `le_clog_of_div_le`
derives `T(n) ≤ a + c * Nat.clog b (n + 1)` from a constant toll and `b > 1`.
Geometric bounds handle multiple equal-size branches.

For balanced splitting, `le_nlogn_of_balanced_le` accepts:

```text
T(0), T(1) ≤ a
T(n) ≤ T(n / 2) + T(n - n / 2) + c * n   for n ≥ 2
```

and derives `T(n) ≤ a * max(1, n) + c * n * Nat.clog 2 n`. Odd sizes, both base cases and
nonmonotone `T` are covered. `isBigO_nlogn_of_balanced_le` exports ordinary mathlib Big-O.
The existing recursive merge sort uses this analysis for its actual call, merge and copy work.

For unequal finite branching, `le_of_sum_rec_le` compares decreasing child recurrences with
a supersolution. The Akra–Bazzi bridges retain mathlib's positivity, rounding and regularity
premises. An upper recurrence is compared against an exact recurrence before applying the
upstream theorem; an upper inequality does not justify a matching lower or Theta bound.

`isBigO_of_sum_rec_le` can construct a mathematical exact majorant when one is not already
available. `p_eq_of_sum_eq_one` identifies its characteristic exponent from the coefficient
equation. Power-toll bounds then distinguish subcritical, critical and supercritical cases:
`O(n^q)`, `O(n^q * (1 + log n))` and `O(n^s)`, respectively. The proofs reuse mathlib
p-series, harmonic bounds and integral comparisons.

Rounded branches use `floor_mul_dist`, `ceil_mul_dist` and `div_split_conditions`.
Bounded rounding errors use `isLittleO_div_log_sq_of_bounded`. Toll regularity should use
the existing mathlib `growsPolynomially_*` theorems; that analytic condition is not the same
predicate as the library's existential polynomial upper bound.

## Legal inputs and growth regimes

`Ram.UniformTimeBound` fixes one program, encoding, admissible input family and result
specification. `Ram.UniformBigO` connects the actual runtime witnesses to mathlib asymptotics
over legal width/input pairs. Total correctness still holds below the eventual threshold.

`Ram.UniformBigOAt` separates the growth expression from the filter describing the regime.
For parameters `n` and `m`, a total-size filter based on `n + m` can express `O(m * log n)`
without requiring both parameters to tend to infinity. Product `atTop` would impose that
stronger requirement. Choose small-parameter shifts to match the intended claim.

`of_terminatesWithin` connects a proved complete execution bound to its mathematical Big-O.
`filter_mono` and `of_isBigO` retain the same execution witnesses. `UniformBigO.reparam`
changes size through an explicit `Tendsto` premise and growth comparison; it changes no
encoding and performs no runtime conversion. An estimate valid only for large intermediate
sizes cannot be used where those sizes remain bounded without further justification.

## Components and executable composition

`Ram.Component` packages a proved implementation and shared interface.
`Component.ofNamed` starts from a named-program contract. Given components implementing
`f : A → B` and `g : B → C`, `q.comp p maps_domain` renames the second function table,
including recursive calls, and sequences the implementations into one program. The proof
retains the actual intermediate representation and uses the same word width.

For scalar envelopes `T`, `H`, `D`, `S` describing time, heap capacity, call depth and result
size, the derived composition has the form:

```text
T(n) = Tp(n) + hull(Tq)(Sp(n))
H(n) = max(Hp(n), hull(Hq)(Sp(n)))
D(n) = max(Dp(n), hull(Dq)(Sp(n)))
S(n) = hull(Sq)(Sp(n))
```

The finite-prefix maximum `Asymptotics.monotoneHull` permits substitution into a nonmonotone bound and
reuses mathlib's `Finset.sup`. It is a proof expression, not an inserted runtime computation.
Complete execution adds the header read and halt once. A change of physical representation
requires an implemented adapter with its own correctness and cost.

`Component.TimeBoundOn` refines time using the full input. Its composition evaluates the
second bound at `f x`, giving `firstTime w x + secondTime w (f x)`. `ResourceBoundOn` does
the same for time, heap capacity and call depth, adding time and taking maximum capacities.
`runs_memory` retains output correctness, an actual complete execution, its time bound and
its address bound in one result. Capacity bounds are not peak live-space theorems.

`PolyTimeComponent` also carries polynomial intermediate size, which is necessary for
repeated polynomial-time composition. Executable many-one reductions use
`Ram.PolyTimeReduction`; composition and `pullbackDecider` reuse the actual component code.

## Complete problem claims

A conditional component is not yet a complete theorem for a published problem.
`Component.Realization` connects every legal input of an already fixed `Ram.Problem` to
the actual encoding, represented initial state, sufficient capacities and required output.
The problem fixes the width policy and size convention; a submitted proof cannot narrow
its domain to make the implementation fit.

`Ram.Certificate` fixes the required concrete bound. Asymptotic certificates additionally
require a nontrivial growth regime: scalar problems supply arbitrarily large legal sizes,
while `AsymptoticCertificateAt` accepts an explicitly nontrivial filter and full-input growth.
The same program and all-input correctness are retained when exporting a mathematical Big-O.

`Realization.toCompAsymptoticCertificateAt` composes full-input asymptotic estimates along
the actual legal-input map. Its `Tendsto` premise justifies use of the downstream estimate;
the result includes fixed program overhead even if the chosen growth terms vanish.

## Existing budget-threading interfaces

Existing coupled proofs remain usable through `Ram.Source.Verification.WP`, `ram_vc` and
`ram_apply`. This total WP passes the actual unused execution budget to a continuation;
sequence cannot restart it. For a supplied ordinary or relational contract,
`ram_apply h reserving r` leaves the additive obligation `blockBound + r ≤ availableFuel`.

For amortized contracts, the initial obligation includes potential and the continuation
retains final credit. `ram_bound [facts]` normalizes proved call and loop lengths, then uses
ordinary arithmetic. It does not choose an invariant, invent a bound, unfold recursive
execution or silently replace logarithmic growth with a weaker linear estimate.

These compatibility tools are useful inside existing time proofs. They are not a reason to
expose budget arithmetic in new mathematical correctness specifications.
-/
