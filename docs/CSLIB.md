# CSLib integration

`integrations/cslib/` is an optional Lake package. The machine kernel and the
root package still depend only on Lean/Std. The integration depends on the local
`ram` package and imports the official CSLib module
`Cslib.Foundations.Data.RelatesInSteps`; no upstream definitions are copied or
renamed as a substitute for that dependency.

## Pinned environment

- CSLib: [`232407ba9e7883e71aa57e046f130f52932fc9c8`](https://github.com/leanprover/cslib/commit/232407ba9e7883e71aa57e046f130f52932fc9c8).
- Lean: `4.28.0-rc1`.
- The CSLib manifest pins mathlib to
  `5352afccd6866369be9de43f5b7ec47203555f44`, the existing search/evaluation
  baseline. No Lean or mathlib version upgrade is needed for this dependency.

The imported CSLib module depends on `Cslib.Init` and
`Mathlib.Logic.Relation`. CSLib's initialization imports its small lint module,
`Mathlib.Init`, and `Mathlib.Tactic.Common`; the lint module uses Batteries and
Lean. The official dependency remains licensed under Apache-2.0; its
`RelatesInSteps` source credits Bolton Bailey. See its
[source](https://github.com/leanprover/cslib/blob/232407ba9e7883e71aa57e046f130f52932fc9c8/Cslib/Foundations/Data/RelatesInSteps.lean)
and [license](https://github.com/leanprover/cslib/blob/232407ba9e7883e71aa57e046f130f52932fc9c8/LICENSE).

## What is connected

`RamCslib.Execution` proves that `Ram.Exec` is equivalent, at exactly the same
step count, to CSLib's `Relation.RelatesInSteps` instantiated with the RAM
transition. It also connects `runExact` to that relation, and proves that
`TerminatesWithin` is precisely `Relation.RelatesWithinSteps` together with a
halted endpoint. Faults are not treated as successful termination.

The actual budget runner is also connected:
`Ram.Cslib.run_relatesInSteps` uses its returned step count and final state;
`Ram.Cslib.run_halted_relatesWithinSteps` exports the budget bound and halted
endpoint when the runner reports success. An exhausted budget or fault does
not become a successful CSLib execution certificate.

`RamCslib.Compiler` exports the optimized, callee-local checked compiler through
`Ram.Cslib.compileChecked_relatesInSteps` and
`Ram.Cslib.compileChecked_relatesWithinSteps`. Their premises use
`LocalCompiler.compileChecked` and `Source.LocalMeasuredExec`, so the measured
calls use each callee's own frame rather than the former global frame size.
These CSLib exact and bounded execution certificates preserve the source output
and remaining input, and count the actual header-read and halt steps. They do
not let a caller supply an alternative operation-price table. The stack-fit
premise remains the compiler's sufficient global-depth bound; it does not
change the local-frame execution count.

This is a connection to CSLib's shared execution and step-bound infrastructure,
not a RAM-to-Turing-machine simulation. In particular it does not claim
`SingleTapeTM.PolyTimeComputable` or `MultiTapeTM.ComputableInTimeAndSpace`.
Those claims require an additional finite-alphabet encoding and a proved
simulation cost. The core's `UniformBigO` is a RAM-specific interface; it is not
an upstream CSLib definition.

`RamCslib.Asymptotics` separately connects mathlib's `Asymptotics.IsBigO` to
the RAM certificate. `UniformTimeBound.bigO_of_isBigO` starts from successful,
functionally correct executions of one fixed program with a concrete bound,
and uses a mathlib Big-O proof about that bound to derive `UniformBigO`.
The encoding, admissibility, word widths, size, and result specification do not
change; total correctness is retained even below the asymptotic threshold.

## Building

Build on 0v0, not on the local computer, from the optional package directory:

```sh
cd /home/vvauted/ram-lean/integrations/cslib
lake build RamCslib
```

Dependency resolution must retain the above revisions. An existing checkout
and normal Lake cache for that exact mathlib revision can be reused; do not
silently resolve to a newer mathlib or Lean toolchain.

Verified on 0v0 under the pinned rc1 toolchain: the optimized compiler exports,
the actual budget-runner bridge, the mathlib asymptotic bridge, and the complete
`lake build RamCslib` all compiled successfully. The existing exact mathlib
checkout and its normal artifacts are reused through a server-local path
manifest; that manifest is ignored so absolute cache paths are not part of the
portable package.

This checks the modules used by the integration, not every module in CSLib.
