# Progress

## Current optimization milestone

The baseline compiler was verified at `0016d68`; `fdd0865` added the fast runner,
named programs, proof interfaces and CSLib connection. The callee-sized compiler
and its complete simulation are now implemented and selected by default by
named programs and public contracts. All compilation and measurements took place
on 0v0 with the unchanged Lean 4.28.0-rc1 toolchain.

The following optimization work now has individual rc1 server verification:

- `Runner`: tail-recursive maximum-budget execution, preserved final states and
  stopping reasons, soundness/completeness for successful execution, and a
  generic exact backend-correspondence theorem.
- `Fast`, `RunProgram`: array/tree-map storage with full instruction, step and
  runner equivalence; reusable prepared executables. Native performance evidence
  for the same array workload is in `PERFORMANCE.md`.
- `Syntax`, `Named`: explicit variable resolution, independent function names,
  forward/recursive/mutually recursive programs, and actual linker correspondence.
- `Contracts`, `ContractFill`: primitive and relational rules, entry-state
  composition, and transfer of heap/I/O postconditions to a budgeted halted run.
- `Problem`, `ProblemArithmetic`: fixed problem-owned specifications, concrete
  budgets and genuinely unbounded asymptotic domains, with a real seven-step
  arithmetic certificate.
- `integrations/cslib`: the official exact rc1-compatible CSLib dependency,
  exact/bounded execution and compiler bridges, and a separate mathlib `IsBigO`
  bridge. The optional package's full server build has succeeded.
- `LocalABI`, `LocalEffects`, `LocalCallSetup`, `LocalCallReturn`: callee-sized
  saved/initialized/restored intervals, actual SP arithmetic, and preserved
  higher registers. Call overhead is derived as `7 * callee.locals + arity + 11`
  in addition to argument, body and result-expression execution.
- `LocalCompiler`, `LocalAtomic`, `LocalExact`, `LocalCall`, `LocalMeasured`,
  `LocalProgram`: complete checked compilation and exact whole-program execution,
  including recursion, without an unresolved call-simulation premise. Increasing
  the reserved-register boundary does not increase the emitted operation counts.
- `LocalCalls`: an observable call overwrites its parameter, restores its caller,
  and preserves a higher caller variable. An unused 200-local function does not
  change the complete 36-step run; the theorem is parameterized by larger bounds.
- `Factorial`: the actual source is now a named recursive program and its final
  execution proof uses the optimized compiler. The exact `37 * k + 37` complete
  count, modular/natural result and uniform linear theorem remain verified.

The public `Ram` umbrella passed the final server build (52 jobs, zero
diagnostics). The native `ram-demo` executable built under the optimized default
compiler (50 jobs) and ran the identical array workloads; see `PERFORMANCE.md`.
Axiom checks on runner completeness, fast-run equality, local-call simulation,
checked whole-program heap preservation, compiled contracts, array fill,
heterogeneous calls, factorial and the complexity boundary found only standard
Lean axioms. The optional CSLib package also passes its complete build.

`Named.Bundle.compile` selects `LocalCompiler.compileChecked`; prepared
executables select `Fast.run`. `Contract` and `RelContract` use `LocalMeasuredExec`,
and compiled contracts and CSLib exports use `LocalProgram`. The older
global-register compiler is retained explicitly as a reference, not selected by
these default paths. Stack-capacity premises remain conservative in the global
register bound; a tight space-complexity theorem is not claimed.

## Earlier verified milestones

The requested structured-language/compiler/proof stack is implemented and
verified on 0v0 with Lean 4.28.0-rc1. The model boundaries below remain explicit;
this does not claim compatibility with arbitrary source languages or word widths.

## Established

- Independent local Git checkout and durable Git repository on 0v0 created.
- Server Lean 4.28.0-rc1 verified; matching existing mathlib revision read.
- Scope, uniform transition-count model, and completion obligations recorded.
- Primary literature and its limitations recorded in `LITERATURE.md`.

## Verified on 0v0, Lean 4.28.0-rc1

- `Word`: fixed word operations, modular and no-overflow arithmetic lemmas.
- `Machine` / `Execution`: executable deterministic transitions, exact execution
  counts, composition/splitting, uniqueness of terminating counts, and the
  executable `runExact` correspondence.
- `Block`: straight-line state transformers linked to real machine execution
  inside surrounding code, using `CodeAt`.
- `Expr` / `ExprCompile`: source expressions, automatically computed variable
  bounds, executable compilation, value and frame preservation, and exact target
  step counts. Compiled multiplication has modular and no-overflow refinements.
- `Source`: structured statements, functions with fresh local frames, recursion
  and mutual recursion, finite source execution, and its determinism theorem.
- `Memory`: partitioned heap agreement, expression read safety, stack-write
  isolation, and source/target expression agreement with a private target stack.
- `Array`: contiguous non-wrapping array representation, reads and single-word
  writes, preservation of other elements, and compiled indexing correctness.
- `Control`: target if/while code layouts, branch/exit/iteration composition,
  including the actual condition, branch, and back-edge transitions.
- `Examples/Arithmetic`: one fixed program reads two words, evaluates a compiled
  multiplication expression, writes the product, and halts. Its entire run is
  proved, with modular and exact mathematical-output specifications. Seven
  transitions are derived from its code, including input/output and halt.

The initial modules above passed individual server checks and a complete
`lake build` (14 build jobs, zero diagnostics) at commit `d01970a`.

`#print axioms` on the expression refinement, source determinism, partitioned
expression compilation, compiled indexing, loop composition, and complete
arithmetic-program theorems reported only `propext`, `Quot.sound`, and (for source
determinism) `Classical.choice`.

## New verified compiler milestone

The following modules pass individual file checks and the complete umbrella
build on 0v0, rc1:

- `ABI`, `Arguments`, `Frame`, `CallSetup`, `CallReturn`: actual argument
  evaluation/buffering, one-word stores and loads, fresh locals, exact SP
  arithmetic, saved return address and caller-local restoration.
- `SafeSource`: source read/write safety and nested-call bounds, with erasure to
  source execution. A depth bound is a stack-space premise, not a time estimate.
- `Effects`, `Atomic`, `Structural`: source effects, preservation of older
  frames, and simulation of assignments, I/O, sequence, branches and loops.
- `Compiler`: executable checked compilation, all statement and function code,
  static arity/lookup validation, and exact code layout. Each recursive function
  body is emitted once, not expanded once per invocation.
- `Call`, `Program`: the entire call/return chain and whole linked-program
  simulation, including recursion and mutual recursion. The final theorem has
  no unresolved `CallsSimulate` premise and proves successful halt plus output
  and remaining-input agreement. Heap safety, stack capacity and code fit remain
  explicit sufficient conditions.
- `Exact`, `CodeLength`: compositional exact-step rules for every structured
  statement, including calls, and the call-overhead formula derived from actual
  instruction lists. Exact call and existence-only call interfaces share one
  frame-restoration proof.
- `Syntax`: natural embedded expression/block/function syntax. Function
  parameters and locals receive register numbers automatically. Three DSL
  examples have checked definitional equalities to their intended source AST;
  these equalities alone do not establish those example programs' correctness.
- `Measured`: source execution indexed by compiler-derived counts, equivalence
  with safe source execution after forgetting the count, exact recursive
  simulation and the full-program `steps + 2` theorem. The indexed count is
  connected to target `Exec`, not extracted from a Prop proof or chosen freely.
- `Contracts`: total correctness and budgets, consequence and sequential
  composition, loop invariants with a decreasing variant or remaining-budget
  potential, and compilation of contracts to actual `TerminatesWithin` bounds.
- `Complexity`: fixed-code bounds uniform over inputs and admissible widths,
  and a concrete-bound-to-Big-O theorem. `UniformBigO` additionally requires
  total correctness for every legal input, even below its asymptotic threshold.
- `Examples/ArraySum`: arbitrary preloaded arrays, a fixed non-unrolled loop,
  modular sum and memory/I/O preservation, and an actual `16 * length + 4`
  block execution. Executing the final halt adds one transition.
- `Examples/Factorial`: natural DSL source, genuine recursive calls and caller
  frame restoration, a fixed 60-instruction program, and exactly `37 * k + 37`
  complete transitions. The output is factorial modulo `2^w`, or the exact
  natural factorial when it fits. Its uniform linear theorem uses numeric `k`
  as size, not the binary input length.

## Final verification

The final server `lake build` completed successfully with 34 build jobs and
zero diagnostics, including both larger examples and the complete `Ram` import.
No local Lean compilation was performed. Source inspection found no `sorry`,
`admit`, `native_decide`, unsafe definitions, or custom axiom declarations.

Server `#print axioms` checked the runner equivalence, compiled multiplication,
array store, exact call simulation, safe-to-measured existence, exact checked
whole-program execution, loop potential rule, compiled contract, uniform linear
bound, array-sum halt theorem, and both factorial natural-result and uniform
linear theorems. All use only `propext`, `Quot.sound`, and (where needed)
`Classical.choice`. No call-correctness or cost-model axiom was introduced.

## Coverage of the original design obligations

| Obligation in `DESIGN.md` | Verified implementation |
| --- | --- |
| Fixed word-RAM and executable transition | `Word`, `Machine` |
| Uniform counting and executable runner correspondence | `Execution`, `Block` |
| Statements, local functions, recursion and effects | `Source`, `SafeSource`, `Syntax` |
| Every construct compiled with preservation and actual steps | `Compiler`, `Call`, `Program`, `Exact`, `Measured` |
| Arithmetic, array/frame lemmas and compositional budgets | `Word`, `Array`, `Frame`, `Contracts`, `Complexity` |
| Same source used for execution and meaningful proofs | `Examples/Arithmetic`, `Examples/ArraySum`, `Examples/Factorial` |

## Deliberate boundaries

- This is a first-order word language, not arbitrary Lean computation. There
  are no higher-order callbacks, early returns, `break`, or `continue` forms.
- Source heap accesses, live stack space, and return-address encodings must
  satisfy the stated conditions. The compiler does not silently add checks.
- The instruction set includes word multiplication; unbounded-integer
  multiplication is not claimed to take one machine step.
- ArraySum is a preloaded-array contract. Its stated time does not include
  external loading. Factorial and Arithmetic include their full I/O protocols.
- RAM transition counts are not Lean-interpreter wall-clock measurements.
