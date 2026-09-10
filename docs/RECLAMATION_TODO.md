# Scoped reclamation and space proofs

Extend the checked allocation path with real reuse of temporary storage. This
queue is not complete when only a reset primitive or a heap lemma exists.
Correctness, reclamation and space claims must describe the same source program
and actual compiled execution. Reuse Lean's well-founded recursion machinery.

## Required implementation

- [x] Restrict the **current** heap to retained object IDs, preserving writes to
  older objects. `Heap.take` and its lookup/contents/shape rules pass on 0v0.
- [x] Provide counted RAM cursor capture/release with register and memory frames.
- [x] Connect release to the retained source heap and existing placement; freed
  cells become available to subsequent allocation without restoring old values.
- [x] Add a scoped source operation with explicit lifetime/escape behavior,
  actual evaluator and correctness rules. Retained locals, returned views and
  suspended callers must not acquire dangling references. Faults and early
  returns need specified behavior, not an implicit heap rollback.
- [x] Integrate scope lowering, readiness, counted simulation and typed linking
  through the existing language and compiler, including loops and calls.
- [x] Expose scoped scratch in the named frontend and mathematical proof rules.
  Keep longer-lived results valid; a fresh result cannot silently survive reset.
- [x] Connect a reusable heap/stack space observation to real execution prefixes,
  including allocation initialization and call/return phases. State whether
  inputs, outputs, metadata and scratch are included; use words explicitly.
- [x] Demonstrate repeated temporary allocation reusing bounded physical storage,
  retained-object mutation, nested/called scopes and a surviving result using
  shared proofs rather than algorithm-specific lowering adapters.
  `Scope.make_runUntil` checks the same named source declaration, with a physical
  envelope of `entryCursor + 1 + 2*n + 2*frameSize`, independent of the call count.
- [x] Build changed modules, affected existing consumers, library and manual on
  0v0; update the public roadmap and push coherent verified work.

Verification: the current `Complexity`, `Examples` and `ComplexityDocs` aggregate
Lean targets pass on 0v0, including the same-source `make_runUntil` theorem.
The source, scope simulation and final runner proofs use only standard Lean
axioms. No additional test framework or local compilation is involved.

## Reuse Lean termination infrastructure

- [x] Generalize the fixed-capture native loop specification from a Nat variant
  to an arbitrary `WellFounded` relation, deriving the old rule with `measure`.
- [x] Expose the general rule through the named loop interface and retain its
  existing consumers. Reuse `InvImage.wf` and Lean's relation constructions.
- [x] Document the existing single `termination_by` argument for pure recursive
  definitions and the existing source contract induction for effectful calls.
  Termination of a Lean definition returning `Part` is not a proof of `Part.Dom`;
  preserve successful-execution obligations rather than adding fuel.

## Boundaries

The selected extension is safe scoped scratch reclamation with surviving outer
storage, not a claim that general tracing GC, reference counting, moving objects
or arbitrary lifetime inference already exists. It must actually reuse memory:
an abstract live-object count paired with the old never-reclaiming executable
does not establish the intended space bound. All still-accessible aliases and
retained caller roots remain part of the safety argument.

Root owns integration and server compilation; contributors own disjoint files.
No local compilation, checksum machinery or unrelated test framework.
