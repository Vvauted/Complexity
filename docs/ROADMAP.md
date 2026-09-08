# Roadmap

Write and verify a high-level program. Automatically derive the register-level
proofs and the guarantees of its compiled execution. RAM is a backend for
implementation and complexity certification, not the language in which an
algorithm author should have to prove correctness.

The [high-level language design](HIGH_LEVEL_LANGUAGE.md) is the architectural
decision for the next phase. It introduces an independently interpreted typed
core, source-level verification, and checked lowering to the existing backend.
This is planned work, not an interface already implemented by `ram_def`.

## The correction in direction

The current named language mainly elaborates into register-based `Stmt/Func`.
Its generated body equations, mathematical result projections and source-cursor
tactics are useful, but do not constitute a complete high-level semantics and
automatic proof transfer.

Therefore, extending a cursor across more RAM WP tactics is no longer the main
roadmap. It may support compiler implementation or existing users. The main
deliverable is a source proof whose connection to the register program is
generated from shared compiler theorems, without an algorithm-specific adapter.

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

## M1 — Independent source meaning and the first automatic proof transfer

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
2. Prove source total-WP and structural verification rules. Establish the
   required semantic `Part`/Std.Do adequacy and `pure/bind` laws where used;
   a thin tactic over the same source rules can precede the full Std adapter.
   Do not assume `mvcgen` supplies termination or compiler correctness.
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

## M2 — Abstract mutable data and arbitrary traversal bodies

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

This completes a useful borrowed-array subset, not allocated-container support.

## M3 — While, recursion and reusable high-level implementation proofs

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

- More source-cursor extensions as a substitute for the independent language.
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

A milestone is done when a user can write the source program and its mathematical
proof without supplying the register-level proof. Backend implementation gaps
belong to the framework, not in the user's theorem.
