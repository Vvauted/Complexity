/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Elaboration

/-!
# Typed source emission with shared buffers and allocation

`source_program P where` declares an independent typed source program from
Lean-style function headers and `do` blocks. The supported types are
`Nat`, `Bool`, `Unit`, Nat/Bool buffers and node references, products and `Option`, with lexical `let` and
`let mut`, assignment, named first-order calls, `if`/`then` with optional `else`,
`while` and `return`.
Only the nearest mutable binding may be assigned; ordinary `let` bindings and
parameters are immutable. `x ← action` rebinds a mutable local to the actual
result of a supported named call, buffer or node read, slice or allocation. Natural arithmetic and
comparisons may be nested in bindings, assignments, return values, conditions
and call arguments. Their operands are normalized left to right into actual
lexical primitive bindings; no host computation replaces the generated operations.
Natural comparisons include `<`, `≤`/`<=`, `>` and `≥`/`>=`; `=`/`==` and
`≠`/`!=` compare either two naturals or two Booleans. Boolean `!`, `&&` and `||`
use actual typed branches. The right operand of `&&` or `||` is evaluated only
in its selected branch, including its normalized intermediate operations.

Products use ordinary pairs and `.1`/`.2` or `.fst`/`.snd` projections. Options
use `none`, `some value` and an exhaustive `match` with `none` and `some value`
branches. The payload exists only in the latter branch; leaving it preserves
the actual heap and outer mutable locals. Expected parameter, binding and
return types supply the type of `none`; otherwise give an ordinary type annotation.
Immutable bindings also accept nested product patterns and `_`, including
`let (x, y) ← call` and `some (x, y)` branches. The right-hand side is evaluated
once; named fields are obtained by actual primitive projections and copies.

Source functions support `for i in [:stop]`, `for i in [start:stop]` and
explicit positive strides `[start:stop:step]` or `[:stop:step]`. Bounds and the
stride are frozen; the index is immutable. A literal or immutable Nat local may
be reused directly, as may an immutable buffer's length in the guard. Other
expressions are captured once. The actual guard, increment and capture work
remain counted. Lean checks stride positivity using `omega`, including dynamic
expressions such as `k + 1`; zero or an unproved positive stride is rejected,
not silently changed into a different range.
`for x in xs` borrows a
fixed buffer view and reads its current cell on each iteration, not a snapshot.
These constructs lower to the existing while semantics and named-loop rules.
Pure finite ranges also generate executable native Lean iteration and its
source correspondence. `source_pure_simp [P.f]` reduces an always-continuing
native range to ordinary fold mathematics without return flags or cursor
bookkeeping. Pure unbounded `while`, `break` and `continue` are not supported.

A named function returning `Unit` may be called directly as a `do` statement.
Other return types require an explicit binding; results are not silently discarded.

`source_program P importing Library, Other where` additionally permits qualified
calls such as `Library.f x`. The imported programs retain their actual bodies,
including recursive calls and transitive imports, in the combined table. The
generated one-step equations use the original library observations through proved
program embeddings, so callers can reuse existing mathematical specifications.
The source handles `P.imports.Library.map` and `P.imports.Library.embedding`
expose the checked relocation for reusable contract-transfer rules, using the
library spelling in the importing clause.
Lean's persistent environment records public headers across ordinary module
imports; it does not supply an implementation or an assumed callee contract.
Compiled realization and instruction bounds remain separate proof obligations.

Each `while` has an actual source guard block, including for compound Boolean
conditions and parenthesized effectful `do` guards. The guard is reevaluated in
the current state; returning its Boolean leaves only the guard. Named loop,
guard and body observations retain complete lexical coordinates and actual
heap effects, and their equations follow from the source semantic rules.
Each named loop also exports `variant_spec`: the author supplies an invariant
and natural-valued variant over named mutable locals and the current heap.
The companion `wellFounded_spec` accepts an ordinary Lean well-founded relation
on the mutable locals and heap; it does not impose a numeric fuel or time budget.
Immutable lexical captures are fixed by generated preservation proofs, not
additional author-maintained invariant fields. This does not infer the
mathematical invariant or turn descriptor preservation into a heap frame.
The named `rel_contract` instead permits a mathematical state related to those
mutable locals and the current heap. Its invariant and well-founded progress
use that model; each normal body exit provides the next related model.

Buffers expose `xs.length`, `let x ← xs.get i`, `xs.set i value` and
`let ys ← xs.slice offset length`. Reads and writes observe the current shared
heap; copying, passing or returning a buffer does not copy its contents. Buffer
parameters and results use the existing `Buffer .nat`/`Buffer .bool` Lean types.
There are no buffer literals, object-identifier constructors or host callbacks.

`NodeRef Nat` and `NodeRef Bool` denote typed immutable-node handles in effectful
parameters, results, products and options. Passing or copying a handle preserves
its identity. `let (head, tail) ← ref.read` reads the actual stored payload and
optional shared tail using `Stmt.readNode`; its generated monadic equation uses
`NodeRef.readM`. The receiver must be a node handle, not an `Option`: match an
optional root before reading it. Reading also supports `let mut` and rebinding;
a missing or wrongly typed node faults without changing the current heap.
`let ref ← NodeRef.cons head tail` allocates one immutable node with a Nat or
Bool payload and a same-kind optional tail, returning its actual fresh handle.
The generated `Stmt.consNode` and `NodeRef.consM` equation neither scan nor
validate the shared tail. Construction also supports `let mut` and rebinding.
These operations do not provide a native List facade. Node reads, construction
and node-reference parameters and results are excluded from the heap-free pure
frontend, including handles nested inside products or options. Finite-machine
capacity and word ranges remain separate compilation obligations.

`let xs ← Buffer.alloc length initial` creates a fresh initialized object in the
actual source heap. The initial scalar determines its Nat or Bool element type;
both operands use the same left-to-right expression normalization as calls.
The generated core uses `Stmt.alloc`, and its monadic equation uses `Buffer.allocM`.
Allocation also supports `let mut` and rebinding an existing mutable buffer.
Even an empty allocation has a fresh identity; returning does not remove its
storage, and a later fault does not roll the heap back. Allocation is effectful
and is rejected by `source_program (pure)`. Finite target capacity and counted
initialization remain separate compilation obligations.

`with_scratch do ...` releases objects allocated inside that lexical block when
its surviving locals and return value do not refer to them. Existing-object
writes remain visible; a return still leaves the enclosing function after
cleanup. Escaping references report the source `regionEscape` fault without
releasing the heap. Named scope bodies and equations use the same source rules;
scope exit is not an implicit return-value boundary or an exception rollback.

The declaration exports `P.signatures`, `P.fId`, `P.fBody` and `P.program`,
together with the ordinary curried observation `P.f` and its equation `P.f_eq`.
The equation exposes one body using ordinary `ExceptT Fault (StateT Heap Part)` notation,
keeping named callee observations opaque. It is not a global simp rule.
`P.f_args` supplies the declared argument environment from ordinary parameters;
`P.f_contract` states a source contract with ordinary curried preconditions and
postconditions. Neither requires callers to write environment projections.
`P.f_onArgs` applies an ordinary curried predicate or bound to that environment.
`P.f_total_iff` connects those contracts to successful source evaluation without
manual environment decomposition. `P.f_spec contract` applies a supplied source
contract with the function's ordinary named arguments in a native `Std.Do` proof.
The caller can pass this specialized theorem to `mvcgen`; no callee body is
unfolded and no contract is selected or invented automatically.
The noncomputable action takes the actual
initial heap and observes `Part (Except Fault result × Heap)`; no empty heap is
supplied implicitly. It is a mathematical proof interface, not a host executable
for `#eval`.
All local signatures and imported references are collected before any new body
is translated, so forward calls and mutual recursion refer to actual entries of the
combined program. This does
not assert termination or accept arbitrary Lean functions as primitives.

Only the existing typed core is produced. Its independent execution gives
meaning to return propagation and missing returns; this module neither imports
a machine backend nor substitutes a host computation for a source operation.

## Implementation modules

This file is the shared import entry point. `Core.Basic` and `Core.Context` hold
the declaration syntax, checked metadata and lexical context. `Core.Expression`,
`Core.Normalize`, `Core.LocalReturn` and `Core.Statement` lower actual source code.
Coordinate, completion, contract and observation builders consume that same
lowering; `Core.Pure`, `Core.Range` and `Core.Correspondence` supply its optional
native proof view. `Core.Emission` fixes declaration order, and `Core.Elaboration`
checks the resulting declarations before registering their metadata.

Helpers in `Complexity.Language.Syntax.Core` are internal to these passes. Public
preparation and elaboration entry points retain the `Complexity.Language.Syntax`
namespace and remain available through this import.
-/
