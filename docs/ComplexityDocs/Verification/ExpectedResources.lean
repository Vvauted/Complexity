/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.ExpectedTimeSpace

/-!
# Expected resources

Import `Complexity.Program.ExpectedTimeSpace` for average-case analysis under a
specified input distribution. This interface concerns the existing deterministic
compiled program. It does not provide internal random sampling or a randomized
compiler bridge.

State `Program.Correct` or `CorrectParsed` independently: correctness must hold
for every legal input, not just inputs sampled by the resource contract.
The specification fixes a family `law : Parameter → PMF Input`, its admissible
parameters and growth expressions before a candidate implementation is selected.
Its positive-mass inputs must be legal. Any application-specific coverage or
correlation requirements belong in the definition and justification of that law.

## Two forms of expected time

`ExpectedTimeSpaceOOn` takes a time target depending only on the distribution
parameter. It bounds expected execution time by a uniform linear envelope of
that target. For example, a parameter may fix the input length while the law
samples the contents.

`PointwiseExpectedTimeSpaceOOn` allows the time target to depend on the sampled
input. It compares expected execution time with the expectation of a uniform
linear envelope of this pointwise target. The right-hand expectation must be
finite: a bound by infinity does not establish the contract. This form preserves
dependencies between sampled fields and other legal input parameters instead
of conditioning away those samples.

Both contracts choose their envelope functions and width overhead before all
distribution parameters. The functions are `IsBigO` of the identity using
mathlib's ordinary asymptotics; constants cannot be chosen afresh per sample.
As with deterministic bounds, a finite legal family alone cannot distinguish
asymptotic classes. Applications needing that distinction must retain an
appropriate unbounded parameter family.

## The observed execution

`Program.actualSteps` observes the unique successful RAM invocation. If no such
execution exists, its cost is `⊤`, not zero. `expectedSteps` is its nonnegative
discrete expectation using mathlib `PMF` and `ENNReal`. Zero-mass inputs contribute
zero even when they fail.

The contracts quantify over input-dependent machine widths satisfying
`timeWidth`. The minimum width function is always available, including for
unbounded support; an impossible common-width premise cannot discharge a bound.
The distribution and growth expressions do not depend on that width function.

Space is bounded for every positive-mass input, not merely on average, and
observes the same execution as the time integrand. It uses the existing
[physical-word footprint](ComplexityDocs/Verification/Space.html), including
input reservation and actual heap/stack accesses. It is not peak reachable-live
memory or native process RSS. For the fixed-parameter contract, `runs_correct`
combines this resource witness with independent functional correctness.

## Reusing existing proofs

`TimeSpaceOOn.to_expected` reuses a deterministic joint certificate when its
time target is constant on each distribution's support. The pointwise bridge
`TimeSpaceOOn.to_pointwise_expected` instead requires finiteness of the expected
linear envelope. For a finite-support PMF, use the machine-independent theorem
`PMF.tsum_mul_natCast_lt_top_of_finite_support`.

The `ExpectedTimeSpaceOParsed` and `PointwiseExpectedTimeSpaceOParsed` variants
retain the fixed specification parser and the actual raw-input execution.
Their deterministic bridges start from `TimeSpaceOParsed`; no algorithm proof
is repeated. Decoding a mathematical specification does not give the program
free preprocessing or preload a second decoded input.
-/
