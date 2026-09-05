# Progress

The active objective is not complete.

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
  This is source semantics, **not yet a full function-compilation theorem**.
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

All current modules passed individual server file checks and a complete
`lake build` (14 build jobs, zero diagnostics). No local Lean compilation was
performed. The current source contains no `sorry`, custom axiom declarations,
unsafe definitions, or `native_decide` shortcuts.

`#print axioms` on the expression refinement, source determinism, partitioned
expression compilation, compiled indexing, loop composition, and complete
arithmetic-program theorems reported only `propext`, `Quot.sound`, and (for source
determinism) `Classical.choice`.

## Next implementation

`CALLING_CONVENTION.md` specifies a concrete finite-register, one-word-at-a-time
calling convention using the existing ISA. It is an implementation/proof plan,
not a verified call backend. The next work is its emitted code, frame-save and
restore lemmas, resource-safe source execution, statement compilation, linking,
and the whole recursive-program simulation proof.

## Still required

- Whole-statement compilation and semantic preservation, integrating the
  established expression and target-control-flow rules.
- Ordinary function/recursive-call compilation and preservation, including
  concrete frames, arguments, return labels, and finite-memory conditions.
- Compositional source-level correctness and cost proof rules.
- Natural source syntax and larger proved programs using loops, arrays, and
  recursive calls through the completed compiler.
- A clean server build and requirement-by-requirement verification of that
  complete language; the current successful build covers only the modules above.

This file records milestones, not a replacement for the requested final scope.
