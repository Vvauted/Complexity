# Bottom-up foundations TODO

Build the missing runtime and representation foundations before expanding the
high-level frontend. The first complete path is one source function allocating,
initializing and returning an array, followed by a call using that array and
another allocation preserving it. Mathematical behavior, actual RAM execution,
representation and counted initialization must describe the same computation.

This is the implementation queue for [M4](ROADMAP.md#m4--allocation-lifetime-and-encapsulated-local-mutation),
with the value/model and compiler prerequisites needed to make it usable.
An unchecked box is unfinished even if a component has a draft implementation.

## 1. Values, heaps and placement

- [x] **Source allocation — Beauvoir.** Add typed fresh initialized objects to
  `Heap`; prove fresh ID, contents, old-object preservation and shape extension.
  Define rooted handles separately from valid accesses; transport rootedness
  through growth and writes. Reuse native Array operations and existing heap rules.
- [x] **Representation transport — Kierkegaard.** Prove placement agreement on
  existing object IDs preserves rooted buffer/value encodings and environment
  matching. Preserve existing scalar/length range obligations; do not assume
  all handles valid or all buffers disjoint.
- [x] **Exact-value boundary — root.** Reuse `ValueFits`, field encodings and
  existing word exactness rules. Make the allocator's length, initial scalar,
  address and capacity obligations explicit. No automatic overflow checks,
  arbitrary precision or host-runtime cost claims.

## 2. Actual arena runtime

- [x] **Allocation code — Confucius.** Implement a monotone allocator using the
  existing structured RAM IR: load shared cursor at address zero, reserve the
  interval, initialize it with actual stores, return its descriptor. Include
  zero-length behavior and derive costs from emitted code, not `Array.replicate`.
- [x] **Arena representation — root / Poincare.** Connect complete existing object
  representation to a positive cursor and fresh interval below `heapLimit`.
  Prove metadata protection, fresh-object placement and old-object framing.
  Use an initialized-prefix invariant during filling, not a premature complete
  representation of the new object.
- [x] **Call and session lifetime — Curie / Kierkegaard.** Supply reusable shared-memory frame
  rules: caller-register restoration keeps the actual cursor and storage.
  Bootstrap is an actual counted store once per session; later calls use the
  returned state. Legacy imports require metadata protection explicitly.
  Actual measured calls can use distinct input/output placements while retaining
  rooted caller locals. Legacy heap-mutating bodies supply their final heap
  representation, explicit cursor frame and containment of final object shapes;
  this is not inferred from `SafeExec` alone.

## 3. Compiler and high-level integration

- [x] Add the typed `Stmt.alloc` constructor and semantics with successful
  termination, result/contents and shape/root preservation rules. Its real
  evaluator, `TotalWP`/VCG rules and source linking are checked. Capacity and
  costs remain outside source correctness; the old fixed-placement theorem
  has not been broadened.
- [x] Add syntax-directed allocation lowering, static code size, call validity,
  local-register frames and linking compatibility using the shared allocator.
- [x] Add allocating-program simulation returning an extended placement
  and actual final heap, composing through loops and recursive calls.
  Transport suspended caller roots and returned descriptors to that placement.
  Keep the same source syntax and execution relation; retain the existing
  no-allocation `RealizedExec` and `ExecutionCost` interfaces. Inline the same
  allocator at five fresh local slots, so old programs' code and function
  indices do not change. Agreement on the whole old object domain plus heap
  growth protects suspended caller roots; do not introduce a second runtime
  stack or explicit ghost stack. `ArenaReady` and `ArenaExecutionCost` index
  the same source execution; the generic measured simulation is checked.
- [x] Transport allocation readiness and exact costs through typed imports;
  retain the shared arena and source contract without a new callee proof.
- [x] Connect allocator local registers, stack footprint and counted execution
  to the existing compiler/ABI and resource interfaces.
  The shared allocator now has a checked five-slot inline instance and local
  caller-register frame. `lowerAlloc_measured` connects actual typed operands,
  the initialized source heap and returned descriptor at `14 * length + 18`
  instructions. `ArenaExecutionCost.runUntil` connects the same counted body
  to the halted runner, including flag initialization and the outer ABI.
  `FunctionArenaRealizable.runUntil` combines independent source correctness
  with readiness without a proposed time bound. Positive word width, exact
  ranges, rooted represented inputs and code/stack capacity remain premises;
  input preparation and one-time arena bootstrap are separate operations.
- [x] Prove the complete allocating-callee/using-caller path, including a later
  allocation and empty output. The checked
  [allocation consumer](../Examples/Language/Allocation.lean) calls `make`,
  allocates again, reads the original when nonempty and returns it;
  `retain_runUntil` retains its actual runner count and represented contents.
- [x] Expose named `Buffer.alloc` in `source_program`. The same consumer's
  `Named.make` and `named_make_spec` use `mvcgen` and ordinary `Array.replicate`
  contents, with no capacity or time premise in source correctness.
- [x] Supply native Array contents/result rules and `mvcgen` specifications,
  rootedness and shape preservation, placement agreement and generic compiled
  transport. These remove per-program register/placement proofs while retaining
  actual heap frames and alias conditions.
- [x] Check the routine [source frame/contract composition rule](../Complexity/Language/Effects/Heap.lean):
  `Stmt.NoCellWrites` for the statement and every callee gives `Exec.heap_prefix`
  and `Exec.contents_frame` at the actual final heap, including faults.
  [`Buffer.Contents.mono_prefix`](../Complexity/Language/Heap/Prefix.lean) reuses
  `List.IsPrefix`. This conservative rule permits allocation initialization but
  rejects every explicit cell write. `Allocation.retained_frame` consumes it.

Further source-level resource inference belongs to [M5](ROADMAP.md#m5--source-level-complexity-and-complete-published-claims),
not this bottom-up completion gate. Mathematical value ranges, capacity and
loop invariants are legitimate author obligations, not unfinished compiler fixes.

## 4. Completion boundaries

- [x] Build the complete `Complexity` library on 0v0 with the pinned toolchain
  (3037 jobs), including allocation-aware linking and the source-frame rules.
- [x] Build all 50 Examples targets individually, then `lake build Complexity`
  and `lake build Examples` (1707 jobs) on 0v0.
- [x] Check every current manual submodule on 0v0.
- [x] Build the final `ComplexityDocs` manual on 0v0 (3101 jobs).
  No local compilation, checksum machinery, custom axioms or `sorry`.
- [x] Update the manual and roadmap against checked capabilities. Keep the
  checked scalar pure frontend separate from unsupported pure loops, mutually
  recursive families and buffers.
- [x] State the actual limits: monotone reserved extent includes metadata,
  retained inputs and cumulative allocation; it is not peak live space. No
  reset, free, GC, persistent immutable-result guarantee or OOM exception is
  implied. Later reclamation needs a separate non-escape/lifetime proof.

Root owns integration, server compilation and status updates. Contributors own
disjoint modules and report exact unfinished obligations; adding a standalone
heap constructor does not complete the allocation milestone.

Checked on 0v0: `Language.Heap.{Shape,Allocation,Prefix}`, `Language.Effects.Heap`, `Language.Rooted` and
`Language.Rooted.Execution`, `Compiler.Language.Placement`,
`Compiler.Language.Arena.{Basic,Frame,Allocation,Execution,Call,Import,Lowering,MeasuredAllocation}`,
`Compiler.Language.Arena.{Realization,ExecutionCost,Verification,MeasuredSimulation,ProgramExecution,Linking}`,
the shared `Compiler.Language.Arena.Simulation` rules,
and `Memory.Arena.{Registers,Basic,Registers.Allocation,Allocation,Inline,Function}`.
The actual allocator body costs
`14 * length + 14` instructions; its complete preloaded function call and halt
cost `14 * length + 69`. Inline typed operand materialization and allocation
cost `14 * length + 18`, including empty allocation. Bootstrap is a separate
three-instruction store.
The typed runner connection and preservation of an existing view through a
later allocator call are checked too. General allocating-program simulation
through loops and recursive calls, the compiled runner, named allocation syntax
and `Examples.Language.Allocation` are now checked. The complete library build
and all 50 Examples have passed, including both aggregate builds after the
source-frame addition. All manual submodules and the final `ComplexityDocs`
build have passed. `Stmt.alloc`, its
source semantics/evaluator/correctness rules, source linking and static lowering
have also been checked on 0v0. Raw imported-call
metadata protection and allocation-aware resource linking are checked.
Scalar, Factorial and Remainder also pass individually with generated native
functions and correspondence. This pure subset covers scalars, self-recursion
and acyclic calls, not pure `while`, mutual recursion or buffers.
