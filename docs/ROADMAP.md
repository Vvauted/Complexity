# Roadmap

Write and verify a high-level program. Automatically derive the register-level
proofs and the guarantees of its compiled execution. RAM is a backend for
implementation and complexity certification, not the language in which an
algorithm author should have to prove correctness.

The [high-level language design](HIGH_LEVEL_LANGUAGE.md) is the architectural
decision for the next phase. It introduces an independently interpreted typed
core, source-level verification, and checked lowering to the existing backend.
The scalar path is under implementation; `ram_def` remains the separate
register-source interface, not the implementation of this new semantics.

## The correction in direction

The existing `ram_def` language elaborates into register-based `Stmt/Func`.
Its generated body equations, mathematical result projections and source-cursor
tactics are useful, but do not constitute the independent high-level semantics.
The new `source_program` path supplies that separate semantics and shared
lowering; its remaining author-facing proof work is described in M1 below.

There are two coordinated development tracks: high-level programming/proofs and
backend proof engineering. The first delivers a source proof whose connection
to the register program is generated from shared compiler theorems, without an
algorithm-specific adapter. The second makes those compiler theorems practical
to develop and maintain. Register-level proof support is active library work,
not merely compatibility maintenance, and does not wait for the language to finish.

The connection layer must also make old-DSL lemmas reusable in high-level
proofs. The old DSL remains an implementation interface for library and compiler
authors, not a second proof obligation for every caller. Reusing its contracts,
representation rules and cost results is distinct from merely allowing foreign
calls or sharing an IR; it should not require changing source semantics.

Source-cursor extensions belong to the backend proof track. They are worth
building where they improve actual proofs, but cannot substitute for the first
track's independent semantics and automatic proof transfer.

One source program can have independent behavior semantics, cost observations
and a compiled representation. This is normal language/compiler layering, not
a second manually maintained algorithm.

## Responsibility boundary

| Algorithm author supplies | Framework/backend supplies |
| --- | --- |
| Ordinary mathematical pre/postconditions | Typed source semantics and sound verification rules |
| Loop invariant and termination measure | Source binding, scope and loop-state composition |
| Callee contracts and genuine alias/extent facts | Parameter/result transport and routine data framing |
| Necessary intermediate range and source resource facts | Word/address realization and concrete capacity translation |
| Sums, recurrences, potentials and bounds | Proved cost of emitted operations, calls and control flow |
| A proof about the high-level program | Automatic lowering certificate and compiled execution theorem |

Algorithm proofs must not mention numeric registers, `State.setReg`,
`Stmt` constructors, function-table offsets, ABI code or measured machine
execution trees. Hiding those obligations in one helper per algorithm does not
meet the requirement.

Real array bounds, overlap restrictions, arithmetic ranges and storage needs
remain meaningful. If automation cannot prove one, the remaining obligation
must be expressed using source values and mathematical facts.

Compiler maintainers and authors of low-level primitives intentionally work
below that boundary. They need documented, compositional register/IR and machine
proof interfaces, with automation for routine mechanics and direct access to
semantic lemmas when extending the compiler. Automatic transfer for algorithm
authors depends on this work; it does not eliminate it.

## What already exists

These foundations are retained, not rebuilt:

| Foundation | Evidence and boundary |
| --- | --- |
| Safe source execution and total correctness | `SafeExec`, `TotalWP` and function contracts establish actual termination without a time budget; their source state is still register-based |
| Verified RAM compilation and execution | Local compiler, `runUntil`, `applyState_spec` and run-step bridges transfer results/effects/costs to the same actual invocation |
| Typed calls and compositional costs | Actual returned words/references and updated state feed continuations; result-dependent upper bounds already exist |
| Mathematical data interfaces | Array/indexed representation, slices, frames, lists, ordering and StateM observations are available |
| Mathematical complexity tools | Existing sums, balanced recurrences, mathlib Akra–Bazzi/`IsBigO`, and potential arguments |
| Frontend pieces and diagnostics | Named parsing, signatures, lexical proof sites and existing RAM tactics can support the new lowering |

Existing consumer evidence must be interpreted accurately:

- [FunctionRun](../Examples/Ram/FunctionRun.lean) has a real executable factorial
  equation, not a reference answer supplied by a proof.
- [ArrayMap](../Examples/Ram/ArrayMap.lean) has real calls/stores and a separate
  linear bound, but the short client proof matches a fixed whole-function template.
- [LowerBound](../Examples/Ram/LowerBound.lean) has a `List.findIdx` result and a
  logarithmic bound; its implementation proof still needs a register-role bridge.
- [ArraySlice](../Examples/Ram/ArraySlice.lean) and
  [FunctionComposition](../Examples/Ram/FunctionComposition.lean) pass real data
  between calls, with representation and capacity conditions.
- [MergeSort](../Examples/Ram/MergeSort.lean) has sorted-permutation and ordinary
  contents/StateM observations, plus a bound for the same invocation; its StateM
  view does not yet provide an independent high-level implementation language.

The [implementation notes](DESIGN.md) retain the existing backend's semantic
boundaries. None of these results alone completes the new source-language layer.

## M0 — Design boundary

Status: specified in [HIGH_LEVEL_LANGUAGE.md](HIGH_LEVEL_LANGUAGE.md);
implementation milestones below remain open.

Decisions:

- One typed first-order core with independent behavior, not `eval (lower p)`.
- Lean-like surface syntax, explicit executable operations, lexical values,
  ordinary mathematical specifications and a shared abstract heap.
- Mathematical `Nat/Bool`, explicit modular words, products and typed borrowed
  views; representation support is implemented in stages, never assumed.
- Budget-free source correctness/termination and a separate cost observation.
- Generic checked lowering to existing `Stmt/Func`, then reuse of the verified
  RAM compiler and runner.
- A thin proved connection to existing `Part`, `StateT/ExceptT` and
  `Std.Do` proof infrastructure, not a second collections/monad library.

Exact binder representation, surface spelling and certificate format are small
implementation choices. They must not delay or weaken the semantic boundary.

## Backend proof track — alongside M1–M3

Status: substantial rules already exist; the following interface and automation
work remains open. Extend those rules for real lowering cases rather than
introducing another backend or a parallel verification framework.

The first return-stage refactor reuses the existing frame and result-buffer
contracts, replacing repeated intermediate-state equalities with direct
composition and a shared reserved-register separation lemma. Its public theorem
signatures, generated code and step counts are unchanged. This simplifies the
proof; no measured compilation-speed improvement is claimed.

[`FramePreserved.frameSaved`](../Complexity/Computability/Ram/Compiler/Effects.lean)
now transports a protected memory interval to the concrete saved caller frame.
The ordinary call proof and the local exact/memory call proofs reuse it instead
of repeating slot-address and no-wrap arguments. Heap effects remain allowed;
the execution model, public call theorems and costs are unchanged.

1. **Register states and frames, starting with M1.** Reuse state-update lemmas,
   `State.LocalFrame`, `Stmt.writtenRegs` and the compiler's matching relations.
   Factor repeated read-after-write, fresh-slot, unchanged-local and saved-frame
   transport into shared lemmas and focused simplification. Support symbolic
   register roles and layouts instead of copying numeric-register arguments.
   Local-register preservation must not be mistaken for heap/I/O preservation.
2. **Calls, results and representation, across M1–M2.** Reuse typed contracts,
   argument/result encodings, caller restoration, shared effects and existing
   ABI proofs. Make lowering cases compose these interfaces without rebuilding
   whole intermediate states. Extend source-cursor navigation across actual
   call continuations, exposing returned bindings from the proved post-state,
   not refreshing old snapshots by assumption. Direct IR and machine proofs
   must remain usable when named-source metadata is absent.
3. **Control flow, simulation and costs, across M1–M3.** Compose existing
   sequence, branch, loop, relocation and measured-execution rules. Extend
   focused simplification for program-counter offsets, `CodeAt`, emitted lengths
   and frame transport rather than rebuilding the simulation framework. Extend
   loop-body/exit navigation where it helps maintainers; retain user-supplied
   invariants and actual effects. Keep budget-free correctness distinct from
   cost composition, while sharing routine structural bookkeeping. Costs of
   emitted code, frames and jumps remain proved, not entered by the tactic user.
4. **Arithmetic fragments, starting with M1.** Package supported arithmetic and
   comparison lowering with mathematical results, intermediate range conditions,
   frame preservation and actual instruction bounds, reusing word arithmetic
   and atomic simulation. Multiplication, saturating subtraction, division,
   remainder and equality now have actual lowering and counted primitive proofs.
   Subtraction masks the wrapping difference with a comparison; division and
   remainder reuse the backend operations' existing zero-divisor semantics.

Immediate existing consumers are the real return-stage proof in
`Compiler/Local/Call/Results.lean` and Map's call → store → loop continuation.
Use them to reduce repeated state/frame transport and manual navigation now;
they need not wait for high-level migration. The new consumers are M1's scalar
call/branch lowering proof, then M2's read/write and loop cases.

**Completion evidence for each extension:** a maintainer proves a real emitted
fragment or lowering case by composing public rules, and its execution/frame/
cost consequences integrate through the shared simulation. Routine register and
ABI obligations close without duplicating a whole execution-tree proof. A local
backend change does not force new algorithmic correctness arguments; changed
code costs still require updated bounds when applicable.

Document the entry points and remaining obligations alongside the real proof.
Tactics remain conveniences over checked theorems, usable separately by compiler
certificates and by humans. Neither tactic count nor a new test harness is a
completion criterion.

Implemented consumers now include the scalar whole-function simulation:
[register bounds](../Complexity/Computability/Ram/Source/Bounds.lean) infer local
operands from actual IR; [layouts](../Complexity/Computability/Ram/Compiler/Language/Layout.lean)
compose compact parameter entry, fresh binding and ordered return reception.
[Shared-state effects](../Complexity/Computability/Ram/Source/Effects.lean) reuse
the existing register frame to cover actual recursive calls. They distinguish
restored caller locals from unchanged memory and streams. These are ordinary
backend lemmas, available without source-cursor metadata or the high-level frontend.

The scalar cost transfer reuses an existing safe assignment's proved endpoint
through `SafeExec.assign_localMeasured`, and transports a callee body bound
through `LocalCompiler.Function.callSteps_mono`. The generic scalar simulation
now proves behavior and its actual count together; erasure supplies the old
budget-free interfaces. There is no second full behavior-simulation induction
to update when a lowering case changes. This is a proof-maintenance reduction,
not a measured claim of faster Lean compilation or faster RAM execution.

## M1 — Independent source meaning and the first automatic proof transfer

Status: in progress, not complete.

- [Typed scalar syntax](../Complexity/Language/Basic.lean) and
  [independent finite execution](../Complexity/Language/Semantics.lean) now cover
  lexical bindings, actual calls, sequences, branches and returns over typed
  locals and a shared heap. Calls restore caller locals but retain the callee's
  actual final heap, including on failure. Determinism
  includes the control outcome; missing returns fault, including for Unit.
- [Source total-WP rules](../Complexity/Language/Verification.lean) support
  budget-free mathematical contracts. The
  [scalar consumer](../Examples/Language/Scalar.lean) now starts with
  `increment_eval` and `boundedIncrement_eval`: generated function equations,
  the helper's result and ordinary Nat reasoning establish the actual result
  `min (n + 1) limit`. The generated `P.f_total_iff` accepts ordinary curried
  preconditions and postconditions and recovers the contract used by lowering.
  Its proof reuses `FunctionTotal.iff_eval` and the generic environment rules;
  the consumer no longer decomposes `Env` or repeats the algorithm proof.
  Direct source-WP rules remain available as a compositional proof interface.
- [Independent partial observations](../Complexity/Language/Eval/Basic.lean)
  retain finite normal continuation, return and fault. At a function boundary,
  `Program.eval` returns `ExceptT Fault (StateT Heap Part) result`: applying an
  initial heap observes both the result or error and the actual final heap.
  Finite faults, including
  missing returns for Unit, are defined errors, while `Part.none` means no finite
  outcome. Successful result equations include termination and observe source
  execution, not a result chosen from a specification or a lowered RAM run.
- [Evaluation composition](../Complexity/Language/Eval/Composition.lean) gives
  equations for skip, return, primitive binding, sequencing, conditionals and
  actual calls. [Continuation equations](../Complexity/Language/Eval/Continuation.lean)
  express the same observation through `Stmt.evalWith`: only normal continuation
  runs the remaining block, and calls use native `ExceptT Fault (StateT Heap Part)` bind.
  This is composition of the existing semantics, not another interpreter.
  The [strict Part adapter](../Complexity/Control/Part.lean) reuses
  mathlib's lawful monad with `open scoped Part.TotalCorrectness`: its native
  `Std.Do.WPMonad` requires a returned value, so divergence cannot prove a
  postcondition vacuously. The
  [source adequacy layer](../Complexity/Language/Eval/Verification.lean) connects
  source contracts to these observations and exception-aware native triples;
  their false exceptional postcondition also rejects finite faults.
- [Named scalar syntax](../Complexity/Language/Syntax.lean),
  `source_program P where`, now supports Nat/Bool/Unit and borrowed-buffer
  functions, lexical `let`/`let mut`, assignment, named calls, conditionals and returns. Nested arithmetic and comparisons
  are normalized left to right into actual primitive bindings, including within
  call arguments and guards. Its generated curried
  `P.f` is a noncomputable `ExceptT Fault (StateT Heap Part) result` observation, not a
  `#eval` runtime. The generated `P.f_eq` exposes one body in ordinary monadic
  notation using the proved continuation equations. Named callees remain
  opaque, and the equation is deliberately not a simp rule: users unfold one
  body explicitly and reuse a callee's specification. The scalar consumer uses
  this frontend while retaining its typed AST definitionally and its public API.
  Pure scalar results are equations between whole actions, such as
  `P.increment n = pure (n + 1)`, valid for every initial heap without a default
  empty heap. Function contracts relate initial and final heaps; their native
  triples retain the initial heap as a ghost.
  Buffer length, read, write and relative slice operations use the same current
  heap. Direct and action-result assignment update the actual locals, including
  across a branch join. Named `while` supplies guard/body equations and an
  invariant/variant rule over the changing locals.
  The same buffer declaration now has compiled execution and cost theorems.
- [Scalar lowering](../Complexity/Computability/Ram/Compiler/Language/Scalar.lean)
  connects Nat/Bool atoms and operations to the existing expression compiler,
  with source range conditions, preserved state and counted machine execution.
  Unit is not represented by a dummy scalar word.
  The [remainder consumer](../Examples/Language/Remainder.lean) implements
  `n - (n / d) * d` and reuses the ordinary Nat remainder identity, including
  divisor zero. Its intermediate-range proof and actual compiled invocation
  need only representable inputs; its separate bound counts this implementation,
  not a hypothetical single remainder instruction.
- [Whole-function lowering](../Complexity/Computability/Ram/Compiler/Language/Lowering.lean)
  and [generic simulation](../Complexity/Computability/Ram/Compiler/Language/Simulation.lean)
  compose lexical binding, sequences, branches, real calls and early returns.
  [Static validity](../Complexity/Computability/Ram/Compiler/Language/Validity.lean)
  infers frames and the reserved-register boundary and proves checked compilation
  succeeds. These obligations are not supplied by algorithm authors.
- [Realization rules](../Complexity/Computability/Ram/Compiler/Language/Realization.lean)
  keep actual scalar ranges and maximum call nesting separate from mathematical
  source contracts and instruction budgets.
  [Execution transfer](../Complexity/Computability/Ram/Compiler/Language/Execution.lean)
  connects them to the existing halted runner, exact returned fields and actual
  body-count observation. The [compiled scalar consumer](../Examples/Language/ScalarCompiled.lean)
  reuses the original minimum proof without a register proof. No new runtime is used.
- Lowering now uses a separate, initialized return flag: every source child and
  external continuation is emitted once, including general early-return paths.
  [Flag-preservation rules](../Complexity/Computability/Ram/Compiler/Language/Control.lean)
  and the core simulation discharge separation from live variables and actual
  result fields. Callee return does not raise the caller's flag. Unit has zero
  result fields; the flag is a real control word, not a dummy result.
- [Exact code-size formulas](../Complexity/Computability/Ram/Compiler/Language/CodeSize.lean)
  connect the structural lowering to emitted RAM instruction-list length.
  Sequence and branch subtrees contribute once; the external continuation has
  one copy plus five wrapper instructions. Calls retain actual argument and
  callee-frame expansion. This eliminates exponential continuation copying,
  but is not an unconditional linear bound in bare source-node count or a
  runtime bound. Static size-composition lemmas now live in the foundational
  local compiler module, without importing its execution simulation.
- [Runtime cost rules](../Complexity/Computability/Ram/Compiler/Language/ExecutionCost.lean)
  now observe the same `RealizedExec`, with no proposed budget or repeated
  correctness/range proof. `callCost` derives actual callee-frame overhead;
  branch and return rules count executed guards and jumps, not both branches'
  static code. [Measured lowering](../Complexity/Computability/Ram/Compiler/Language/MeasuredSimulation.lean)
  proves the count equals the existing local compiler's executed transitions.
- [Cost determinism](../Complexity/Computability/Ram/Compiler/Language/CostDeterministic.lean)
  is independent of word width, call capacity and execution-proof choices.
  It follows the independent source trace, without positive-width or encoded
  input premises. Every realized source execution admits this observation.
- [Cost publication](../Complexity/Computability/Ram/Compiler/Language/CostExecution.lean)
  identifies the existing `bodyTime` and combines a separate `FunctionCostBound`
  with source correctness/realizability in `FunctionRealizable.runUntil_le`.
  Returning-body wrapper work and internal calls are included in the body;
  outer call-and-halt work is added exactly once.
- [Structural bound rules](../Complexity/Computability/Ram/Compiler/Language/CostBound.lean)
  let the scalar consumer compose primitive, return, branch and helper-call
  bounds without case analysis on `ExecutionCost`. `StmtCostBound` bounds the
  same realized execution; `FunctionCostBound.of_stmt` adds the returning-body
  wrapper once. Call rules can reuse an existing result contract when the bound
  needs it, but do not require re-proving the mathematical minimum. Applying
  these rules is now automated for the scalar uniform-bound fragment; actual
  arithmetic inequalities remain ordinary mathematical proof work.
- [Structural proof tactics](../Complexity/Computability/Ram/Compiler/Language/Tactic.lean)
  open ordinary arguments and compose realization/cost rules in the existing
  scalar and nested-remainder consumers. Realization reuses supplied callee
  contracts. Cost selects only the executed branch when the guard follows from
  source values and local facts; otherwise it uses a uniform maximum. Uniform
  call-continuation bounds need no duplicate correctness proof. The recursive
  factorial now uses the same structural pass with its supplied induction
  hypothesis. These tactics neither maintain a price table nor infer invariants,
  arbitrary callee specifications or recursive bounds.
  Without `using`, they stop at calls. `ram_source_call using resource, specification`
  consumes one selected pair of contracts and stops at the next call, carrying
  the actual result and final heap. The two-buffer consumer uses separate
  contracts for its distinct contents, with ordinary frame reasoning between
  calls; source argument and result-scope transport remain inside the tactic.

Next, alongside the lemma-transfer bridge and borrowed-buffer integration:

1. Build shared-specification and source proof automation on the generated
   one-step equations and strict Std.Do adapter. The scalar correctness proof
   now uses named arguments, actual call results and ordinary mathematics, and
   generated contract conversion hides typed argument packing. Support reusable
   operation specifications without making recursive unfolding a global simp
   rule or claiming automatic discovery of mathematical proofs.
2. Generate structured realization and cost obligations from the same source
   constructors and shared callee contracts. Shared cost rules now hide execution
   case analysis, and the initial scalar tactic now applies them and opens
   arguments automatically. Extend beyond its supplied-callee and uniform-cost
   fragment while leaving actual range, call-nesting and cost inequalities
   visible. Reuse checked rules without per-program simulation
   adapters or manually supplied instruction prices. The executable observation
   remains the existing compiled runner, not the noncomputable source `Part` value.

The source proof interface must be judged on mutable composition, not just
surface syntax or a short scalar equation. The native buffer specifications in
`Language/Eval/Verification` preserve the current heap for reads/slices and give
both the actual write equation and updated `Array.set` contents for writes.
This lets existing alias/frame lemmas remain usable without assuming all views
are disjoint. Generated `P.f_spec contract` now applies a supplied contract to a
named function's ordinary parameters through native `mvcgen`. The buffer consumer
reuses `clamp_total` without unfolding its helper; initial/final heaps and actual
results remain in the rule. The
[two-buffer composition](../Examples/Language/TraversalComposition.lean) now
calls the existing mutating traversal twice with these contracts. The first
frame supplies the second call's current input, and the second frame preserves
the first result. It unfolds neither callee body. `Unit` functions can now be
called as ordinary statements without unused result bindings.

`Buffer.PreservesOutside` now exports preservation of initially valid disjoint
views, including disjoint intervals of one object. Its write and composition
rules feed the traversal's total source contract and the same represented final
heap of its compiled invocation. The existing array result and instruction bound
are unchanged; no ownership/no-alias restriction or second backend proof is added.

Before broadening the surface further, close these connected gaps:

- Automate selecting supplied effectful-call contracts and their contents/frame
  consequences in nested traversals. Sequential calls now compose these facts,
  but the caller still chooses the contract and its mathematical contents.
- Complete named calls across independently declared source programs. Typed
  signature maps, call renaming, actual-body embeddings and closed-table linking
  now preserve finite execution in both directions and therefore the complete
  partial observation. The [linked consumers](../Examples/Language/Linking.lean)
  reuse the existing recursive factorial and mutable traversal proofs, including
  their actual final heaps. Next resolve imported functions in the frontend's
  combined signature table, generate caller equations and transfer compiler
  realization/cost rules through lowering. A closed-table append creates no new
  call edges; source behavior equality alone establishes no target cost equality.
  Do not substitute host callbacks or copied implementations for source linking.
- Expose ordinary loop locals, current contents and return outcomes to invariants.
  Scope/state plumbing belongs to shared rules; the invariant, termination
  argument and algorithm-dependent inequalities belong to the author.
- Validate behavior, realization and cost on the same source declaration.
  Passing source semantics alone does not establish its compiled execution.

These priorities refine M1–M3; they do not remove products, loops, recursion,
allocation or compiler automation from the intended language. The named while
frontend now supplies an ordinary-local invariant/variant interface. Its first
complete traversal proof composes native operation specifications, using shared
strict `StateT` adequacy instead of unfolding WP or partial-state binds. Further
automation should select and compose supplied contracts without guessing their
mathematical content.

The present cost interpretation concerns successful realized executions.
It is not yet instrumentation of every unrestricted source execution.
Borrowed-buffer operations and typed effectful-guard loops have their own
lowering and cost observations. The loop potential rule follows actual current
states. The first named traversal now composes those bounds through the actual
compiled invocation; more convenient named-loop cost proofs and indexed
traversal remain M2–M3 work.

Complete function bodies now omit their redundant empty final dispatch. Exact
code-size comparison proves a three-instruction saving with the same register
bound; measured simulation changes the function wrapper from `+5` to `+2`.
Generic statement wrappers and ABI charges retain their original conventions.
Further flag-check removal or no-return specialization needs its own proof and
revised costs. The current size-safe lowering
can add instructions and enlarge frames compared with small CPS examples;
smaller code on branching families is not a claim of universally faster runs.

Do not postpone the first buffer operation until scalar automation is perfect:
real calls, heap effects and loop invariants must guide that automation. M1 is not complete merely
because the scalar surface, semantic observations, static compilation and
functional transfer now exist; shared proof and realization/cost automation
remain part of its completion gate.

Build one complete scalar path before extending the surface language broadly.
The first executable subset is Nat/Bool literals, addition/comparison, lexical
binding, calls, branches and terminal scalar returns. Additional types and
operations are enabled one construction at a time only when their semantics,
lowering, proof rule and cost connection are ready. Unsupported nodes are
rejected explicitly; there is no placeholder code or user-supplied RAM proof.

1. Define the typed core, lexical values and independent finite execution,
   distinguishing normal continuation, return and fault. Support scalar
   operations, binding, sequencing, both branches, first-order calls and
   terminal returns. Prove source determinism and proof-independent observations.
   Product encodings and further arithmetic operations follow the first scalar
   transfer; completing all value types is not an M1 prerequisite.
2. Reuse the source total-WP rules, semantic `Part` equations and scoped
   Std.Do interpretation to generate source verification conditions. Their
   adequacy and `pure/bind` laws justify the interface; `mvcgen` does not supply
   missing termination, operation specifications or compiler correctness.
3. Implement lowering and the reusable source-to-IR simulation cases. Generate
   checked certificates for concrete declarations; infer static layouts and
   discharge their register/ABI obligations internally.
4. Connect source arithmetic to the word backend through source-level range
   conditions. When added, subtraction/division/modulo retain Lean's saturating
   and zero-divisor semantics through proved, charged implementations; explicit
   Word programs retain modular behavior. No proof-directed optimization is
   required for the first lowering.
5. Derive the first backend cost interpretation and its adequacy from the same
   lowering. Include actual operand, call/frame, branch and return work.

**Completion evidence:** an actual helper-call/returned-value/branch program is
proved at source level and receives compiled behavior and time theorems without
a register proof or a whole-function template equality. General construction
rules are proved before the consumer is discharged.

A `body_eq := rfl`, successful parser expansion, or a source correctness
predicate defined through the target evaluator does not complete M1.

## Reusing old-DSL lemmas in the connection layer — alongside M1 and M2

Status: in progress. The existing old-DSL function contracts, measured calls and
call-renaming theorems are reusable. `Compiler.Valid.link_of_callsValid` supplies
static composition when a new front table calls an appended old module; unlike
sequential component composition, it does not run the old module's entry block.
Static linking alone does not transfer a mathematical theorem.

The initial `Contract` and `TimeBound` bridge modules now transport result
properties and fixed-width time bounds for the actual `lowerFunc` invocation.
They retain source realization and input representation premises. They do not
yet transfer arbitrary old implementations or establish the consumer gate below.

1. Put transfer rules under `Compiler/Language`, importing both independent
   source semantics and old-DSL proofs. Keep RAM imports and implementation
   selection out of `Language`'s mathematical semantics. Do not add source
   external-function forms solely to reuse existing lemmas.
2. Transfer existing result contracts, representation/frame facts and conditional
   time bounds through a proved correspondence with the actual implementation.
   Encode/decode, routine framing and source-to-target bookkeeping belong in
   reusable bridge rules, not in a new adapter for each algorithm.
3. Distinguish transfer directions. Existing forward simulation can transport a
   realized source execution to the target, where an old contract supplies its
   result property. It does not infer source termination from target termination.
   Removing the source existence premise requires a separate reverse/progress
   theorem, not an implication used backwards.
4. Keep correctness independent of time. Old bounds apply to the same actual
   code or through a proved costed transformation, not merely equal results.
   Preserve real word-range, heap, aliasing and capacity premises; caller-local
   restoration does not imply unchanged shared state.

**First completion evidence:** a real high-level consumer uses a generic bridge
to obtain a result property or a cost bound from existing old-DSL lemmas, without
re-proving that fact through source constructors or writing a register adapter.
The source behavior remains independent and the transferred theorem concerns
the actual implementation, not an assumed whole-function equality.

Apply the same bridge to M2's helper-call/branch/store loop and existing array
representations. Selecting an old implementation for a high-level library call
is additional connection-layer work: it requires a verified implementation and
cost correspondence, not an arbitrary host callback or a dummy source body.
Directly reuse mathlib mathematics when no machine correspondence is needed.

## M2 — Abstract mutable data and arbitrary traversal bodies

Status: the independent shared-object foundation is implemented in
[`Language/Heap`](../Complexity/Language/Heap.lean). Typed native arrays,
checked views, reads/writes/slices, different-object preservation and overlapping
alias observations are proved. `Buffer.Contents` gives a view its ordinary native
array contents; reads use `getElem`, writes use `Array.set`, and overlapping views
observe the same update. The
[RAM heap relation](../Complexity/Computability/Ram/Compiler/Language/Heap.lean)
represents complete objects using a fixed proof-level placement. It preserves
actual aliases, object-cell separation and legal empty endpoints through reads,
writes, parameter binding and caller restoration. It is not a runtime object
table or a source-statement lowering theorem. The
[operation bridge](../Complexity/Computability/Ram/Compiler/Language/HeapOperation.lean)
executes successful source reads and writes with actual dynamic RAM expressions,
preserving the same heap relation and counting operand evaluation through the
existing measured compiler. These rules do not implement source faults or add
runtime validity checks.

The same source execution and function contracts carry this heap. The compiler's
existing layouts now index actual fields uniformly, including parameter packing,
fresh call receivers and result lookup. Buffer types and statements now exist;
their whole-compiler and actual-runner integration is checked.
Mutable local bindings and assignments now have native proof equations, shared
realization/cost rules and generic lowering. The existing scalar consumer assigns
inside a branch and observes the result afterward without changing its mathematical
specification. The buffer consumer rebinds a mutable descriptor to a real slice
result and retains its array-update specification. Layout regularity and update
preservation are compiler lemmas, automatically supplied by generated functions;
buffer self-assignment remains allowed. The named while traversal now has source
correctness and termination proofs, a compiled invocation theorem and an
independent linear instruction bound. Its strengthened source and compiled
contracts also retain preservation of disjoint borrowed views. The general
indexed-traversal interface and automatic composition of effectful helper
contracts remain open.

`boundedMapPair` reuses that exact traversal twice, including when the two
disjoint views belong to one object. Its source contract retains both results
and all observations outside both views. The
[compiled composition](../Examples/Language/TraversalCompositionCompiled.lean)
reuses the first callee's frame to establish the second callee's input at the
actual intermediate heap. `StmtCostBound.call_seq` hides routine call/skip
state transport and charges the actual normal dispatch. Both callee bounds,
two levels of nested calls and the full halted invocation are composed without
reopening either loop. Automatic contract selection and named cross-program calls
are not supplied by this same-program consumer. The separate source linker now
transfers this traversal's complete native action and frame to a combined table;
compiled resource transport through that embedding remains open.
The staged `ram_source_call` interface now hides repeated argument-environment
opening and structural call/sequence composition in this consumer's realization
and cost proofs. Each call takes separately supplied resource and source
contracts; the next call is left for its own contracts. Uniform numerical
continuation bounds retain actual result/heap postconditions. Real disjointness,
frame consequences and the final cost inequality remain visible. General
result/state-dependent numerical bounds still use the explicit rules. Next,
improve named-loop composition and supplied-contract selection; do not erase
the source proof's real dependence on each frame.

The [buffer consumer](../Examples/Language/Buffer.lean) uses native operation
specifications to prove its ordinary `Array.set` result. Its
[compiled theorem](../Examples/Language/BufferCompiled.lean) reuses that proof,
derives the read cell's range from the supplied heap representation, and retains
the actual final heap and two returned descriptor fields. Its independent bound
charges the read, real helper call, write, length, slice and return. No additional
non-alias condition or algorithm-specific register proof is imposed. This is one
read/write path, not the traversal completion gate below; its helper is still
pure and its returned slice covers the entire view.

The source state contains typed locals and the
shared heap. Calls restore caller locals while retaining the actual callee
heap; scope exit preserves updates to outer locals and the current heap.
This state feeds the existing execution and proof interfaces, not a parallel
language. The present scalar instructions preserve arbitrary heaps; that fact
must not become an assumed frame rule for future effectful instructions.
Direct source assignment is implemented independently of any optional SSA
normalization. Typed loop guards now reevaluate in the actual current state;
their source rules carry updated locals and heap, and their cost includes the
final false guard as well as successful iterations and early returns. The
frontend must preserve this behavior: normalization cannot move a changing
guard outside the loop.

1. Give borrowed objects/views independent heap semantics with actual aliasing.
   Prove read/write/slice and local-frame rules using ordinary contents.
2. Relate those objects/views to existing RAM representations. The compiler
   handles descriptor fields, address arithmetic and receiver updates.
3. Provide source `for` rules for arbitrary bodies and captured iteration
   ranges. Each iteration reads the current heap; no implicit input snapshot.
   Expose iteration index and source locals directly to mathematical invariants.
4. Compose helper contracts, returned values, branches and writes in the source
   proof. Lift cost rules over the same arbitrary body and real execution order.
5. Report unproved bounds, range and actual overlap requirements at the source
   operation. Routine preservation and representation transport stay automatic.

**Completion evidence:** directly express the design's helper-call → branch →
store loop, with a transformed-prefix/unread-suffix invariant and an independent
bound for its compiled execution. It must not be reduced to a newly invented
`MapWithBranch.function` template. Reuse ordinary List/Array identities.

The [named while traversal](../Examples/Language/Traversal.lean) and its
[compiled invocation](../Examples/Language/TraversalCompiled.lean) now discharge
the behavior, termination and independent linear-bound parts of this gate on
the actual helper/branch/write program. They use native array identities and a
generated variant rule with fixed captures. Compiled realizability reuses the
source termination proof; cost composition reuses its array invariant, without
a second array-correctness proof. Native operation specifications and strict
`StateT` adequacy remove routine WP/bind unfolding from the source proof.
The outside-buffer frame is now public: it preserves initially valid disjoint
views, including slices of the same object, at the same actual final heap. Its
proof reuses the existing mathematical round and the actual write equation;
the old result-only theorems project from the stronger source/compiled contracts.
An indexed traversal interface remains open. Fixed-capture transport is shared,
and one native round contract supplies the same guard/body facts to all three proofs. Selecting
and composing supplied contracts still need better automation.
This first complete invocation does not finish M2.

This completes a useful borrowed-array subset, not allocated-container support.

## M3 — While, recursion and reusable high-level implementation proofs

The typed core now has effectful-guard `Stmt.while` and six finite execution
cases, including guard/body faults and missing guard returns. Source
`TotalWP.while_wellFounded` and `while_variant` measure progress over the whole
guard/body cycle; false exits and early returns preserve their actual final
state and require no further descent. `Stmt.action` is a state-preserving view
of the same observation, not another interpreter.

The native [loop equation and specification](../Complexity/Language/Eval/Loop.lean)
reuse the existing strict Part/StateT interpretation. Generic lowering emits
the guard and body once each; its measured simulation preserves updated locals,
heap and enclosing return control. Runtime cost distinguishes false exit, normal
iteration and early return, including the final guard. `StmtCostBound.while`
composes state-dependent guard/body bounds with a remaining potential, without
using that potential as execution fuel or a source termination premise.

The [realization loop rules](../Complexity/Computability/Ram/Compiler/Language/Realization/Loop.lean)
can now reuse already proved source termination and postconditions. The extra
round obligations concern operation ranges, call nesting and preservation of
their admissibility invariant, not a second decreasing measure. The
[ordinary-local cost bridge](../Complexity/Computability/Ram/Compiler/Language/CostBound/Locals.lean)
reuses actual guard/body observations and source invariant preservation; it
neither re-proves contents nor defines a separate cost interpreter.

The surface now accepts `while` and emits actual named guard/body/loop
observations, their one-step equations and a normal-continuation theorem.
Pointwise coordinate equations keep equivalence proof fields opaque, and a
lexical-position frame preserves immutable captures automatically. The generated
`variant_spec` takes an invariant and natural-valued variant over named mutable
locals and the actual heap. The read/helper/branch/write traversal now consumes
it to prove finite success and the complete native array-map result, without
an `Env` or register argument. Its compiled consumer now establishes the actual
halted invocation and a separate linear bound. This closes the first named-loop
behavior/cost chain, not general loop-proof automation. Do not substitute an
opaque native loop or a user-maintained host implementation.

Fixed-capture realization and cost rules now keep immutable values out of those
invariants too, reusing the generated lexical frame through the connection
layer. The compiled traversal no longer supplies capture-preservation equations
or dedicated result-uniqueness proofs. Its ordinary guard/body contracts feed
the same actual outcomes into correctness and resource reasoning through the
shared strict `StateT` postcondition rule.

The traversal now proves one native `round_spec`: it records the mathematical
guard decision, then the body contract at the actual post-guard locals and heap.
Its source loop proof and separate resource proofs reuse this same statement.
The resource proofs use the existing strict `StateT` postcondition rule to
extract its facts; the compiled proof no longer repeats post-guard index/heap
substitutions and array-bound reconstruction in five obligations. No special
round-specification framework or second execution relation is introduced.

The shared [native consequence rule](../Complexity/Control/Triple.lean),
`Std.Do.Triple.mono`, reuses WP monotonicity and composes with Std's `Triple.and`.
The traversal's `loop_spec` and `loop_frame_spec` now combine result and frame
facts for the same action without unpacking `Part` execution witnesses. Their
public statements, `round_spec`, source program and costs are unchanged. This
removes proof plumbing, not the author's invariant, descent or frame argument.

Named function contracts can now be passed to `mvcgen` through generated
`P.f_spec` rules, including sequential mutating callees. The next step is
contract selection and generated loop views/frames, which remain explicit. Preserve
the actual heap, source range conditions and cost inequalities. Keep
RAM-specific rules out of source semantics and syntax; simplify existing proofs
rather than introducing another implementation or whole-loop template.

The shared ordinary-local observation now retains all lexical values and the
actual heap on every exit. Its well-founded and natural-variant specifications
reuse the same source loop rule, and its continuation bridge distinguishes
normal continuation from return and fault. Generated observations use these
same shared composition equations. The fixed-capture variant
rule now keeps immutable values out of the author's invariant, using a proved
local frame, and the named frontend now instantiates it. The full lossless
lexical view remains available: a hidden saved condition cannot be recomputed
after a mutable operand changes, and the proof view cannot simply drop lexical
slots. Preserving a buffer capture preserves its descriptor, not its heap cells.

`FunctionTotal.verify_wellFounded` supplies complete callable contracts at
smaller mathematical indices, reusing ordinary well-founded induction and the
existing source body rule. The index may select one function or mutually
recursive functions with different signatures. The
[named factorial](../Examples/Language/Factorial.lean) now demonstrates the
ordinary parameter-induction path: its real self-call returns mathlib's
`Nat.factorial` and preserves every initial heap. Its
[compiled consumer](../Examples/Language/FactorialCompiled.lean) now reuses that
proof and the shared lowering to establish the actual halted invocation, returned
factorial and a separate linear instruction bound. Representable factorial
results bound the intermediate values; `n` nested calls and space for the outer
call remain distinct from the instruction budget. The realization induction
uses `ram_source_realize (input)` with the recursive contracts, leaving the
same mathematical range argument without manual argument-environment or
statement-goal conversion. The cost induction uses
`ram_source_cost (input)` to open ordinary parameters without manual `Env`
unpacking; the author still supplies the induction hypothesis and arithmetic.
Known base/successor guards are selected by the structural cost tactic, and
`callCost_eq_add` keeps compiler-derived call overhead separate from the
recursive body count.
The bound is linear in numeric `n` in the word-RAM model, not binary input length
or arbitrary-precision multiplication cost; this does not complete M5.
The example does not consume the generic contract rule or demonstrate mutual
recursion. Convenient generated recursive contract hypotheses and an effectful
recursive consumer remain open. Neither correctness route requires a proposed
instruction budget or call-stack depth; compiled realizability and cost are
separate obligations.

1. Provide well-founded source `while` and recursive-call rules; user invariants
   and recursive hypotheses concern source values, not backend state.
2. Complete their generic lowering and cost proofs, including loop exits and
   nonterminal returns. The return-control design from M1 must compose through
   nested blocks/loops. Add tagged optional results and `break/continue` with
   proved encodings/control behavior when their consumers are introduced.
3. Derive source-level call-nesting/storage obligations separately from time.
   Translate sufficient bounds through the compiler's inferred frame layout.
4. Migrate Search as a different loop shape, then recursive MergeSort as a
   multiple-buffer and recursive-call consumer.

The pinned Lean runtime implements native `while` through the partial
`Lean.Loop.forIn`. Accepting that syntax is not a proved mathematical unfolding
rule for the source loop. Derive loop equations and well-founded correctness
from the same source `Exec`/`Stmt.eval`, preserving the guard's actual final
locals and heap, then connect them to the existing strict Part WP. For bounded
traversal, reuse `Std.Do.Invariant`, `Invariant.withEarlyReturn` and the existing
`Spec.forIn_range`/`Spec.forIn_rco` rules after proving the source observation
correspondence. Iterate indices and read the current buffer, not a snapshot of
its contents. A second user-maintained StateM algorithm is not this bridge.

**Completion evidence:** Search's algorithm proof uses `lo/hi/mid` and array
contents without a `Registers` bridge. Recursive sort composes source contracts,
ordinary split/merge mathematics and a separate recurrence. Register allocation
changes do not require new algorithmic reasoning.

The core semantics/proof modules remain independent of RAM imports. Adding more
display names to the old `SafeExec` goals is not a substitute.

## Cost-interface work alongside M1–M3

The goal is separate correctness and cost proofs, not duplicated register
navigation or a mandatory second proof of all result contents.

- Establish erasure/instrumentation for the cost observation over the same
  source program. Source behavior cannot inspect cost or a proposed budget.
- Derive weights/overheads from the selected lowering and actual frame layout.
  User-chosen prices are not accepted as RAM costs.
- Support result/state-dependent continuations using existing typed time rules.
  Mutable traversal costs follow actual elements, state and evaluation order.
- For bounds depending only on sizes, use proved shape/length/frame consequences
  of contracts. First simplify MergeSort's information needs without changing
  its admitted domain; then prove content-independent lower-operation bounds
  where possible. Do not simply delete merge/copy/time-import premises.
- Prove an upper-bound connection in the direction needed for target steps.
  Forward simulation plus source totality and target determinism supports the
  initial runner theorem. A target conditional-bound theorem without source
  totality needs completed-trace reflection or equivalent adequacy.
- Reuse mathlib recurrence/asymptotic and existing amortized tools. Add varying
  exact-cost or source-level potential conveniences when a real consumer needs
  them, not a parallel catalog of wrappers.

**Completion evidence:** users prove mathematical cost inequalities for a source
program and obtain a theorem about that same compiled invocation. They neither
price primitives manually nor unfold ABI definitions. Genuine recurrences,
potentials and data-dependent facts remain visible.

## M4 — Constructing and returning data

A pleasant language must eventually create results, not only borrow preloaded
arrays. This is scheduled work, not supplied by the abstraction in M2.

- Implement minimal region/arena allocation, initialization and source freshness,
  with real target operations, storage bounds and costs.
- Support returning live allocated objects and composing their representations;
  do not introduce reclamation without lifetime rules.
- Complete useful structured results and collection operations through proved
  encodings. Reuse standard Lean/mathlib types as mathematical views.
- Provide actual input/output conversion when it belongs to the declared runtime
  boundary. A host loader outside that boundary must be labeled as such.

**Completion evidence:** one source function constructs and returns a container,
and its behavior, allocation/initialization and total invocation cost are
connected to the real backend. No host-side constructor silently supplies it.

## M5 — Complete problem-level claims and further analysis

Use the existing problem/encoding/uniformity interfaces for a real high-level
implementation. Fix its input encoding, size measure, width policy and runtime
boundary; quantify one source program over the legal input family.
Use a fixed compilation scheme and backend/width policy for that family, not
a different synthesized program for each input, execution witness or proof budget.

A fixed-width demonstration plus an `IsBigO` theorem for a natural-number budget
does not by itself establish that complete problem-level claim. Preloaded
memory is an acceptable convention if stated, not a hidden loader theorem.

Later space claims need actual observations of live storage and lifetime.
Cross-model results need costed simulations. Neither is a prerequisite for
removing register proofs from algorithm-author work.

## Work not to make the mainline

- Treating source-cursor extensions as completion of the independent language,
  or treating the high-level language as a reason to stop backend proof work.
- More short mathematical wrappers around already completed RAM proofs.
- A new algorithm-specific register adapter for every changed loop.
- Arbitrary Lean compilation, closure conversion, bignums or a new ownership
  calculus before the basic source/verification/lowering path works.
- New machine models, complexity-class catalogs or unused recurrence variants.

Keep compatibility with existing programs, proofs and dependency pins. CSLib is
not required. New compiled code must have its own behavior/cost connection;
do not inherit old exact constants from result equality.

## Working discipline

For each milestone: prove shared semantic/compiler rules, apply them to a real
consumer, and assess the complete author proof rather than only its final
statement. Use actual Lean checks on 0v0 for implementation work; no local
compilation, checksum machinery or unrelated test framework.

Design-only updates do not require a Lean build. Document planned interfaces
as planned and keep the existing manual honest about current functionality.

A high-level milestone is done when an algorithm author can write the source
program and its mathematical proof without supplying the register-level proof.
The backend track separately requires usable, reusable proof interfaces for the
people establishing that transfer. Backend implementation gaps belong to the
framework, not in the algorithm author's theorem.
