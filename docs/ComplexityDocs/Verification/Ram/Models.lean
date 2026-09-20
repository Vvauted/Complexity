/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Ram.ArrayArguments
import Examples.Ram.ArrayCount
import Examples.Ram.ArrayMap
import Examples.Ram.ArraySlice
import Examples.Ram.ArraySliceProperties
import Examples.Ram.ArraySum
import Examples.Ram.Factorial
import Examples.Ram.GraphDegree
import Examples.Ram.Verification

/-!
# Mathematical models for word-RAM programs

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Use mathematical theorems at the interface

Once you have a refinement, prove properties of `f` using ordinary Lean and mathlib.
`Ram.Source.Refines.spec` transfers a theorem about `f x` to the implemented result.
`Ram.Source.Refines.with_postcondition` retains the property in the representation for
subsequent composition.

Reuse an operation's existing contract before unfolding its body. In particular:

- `Ram.Source.Refines.seq` composes two refinements through their shared intermediate model.
- `Ram.Source.Refines.congr_fun` changes the model by a proved equality of functions.
- `Ram.Source.Refines.equiv` changes mathematical coordinates through an equivalence.
- `Ram.Source.Refines.transfer` handles related, possibly lossy models when the functions
  respect the chosen relations.

The [graph-degree sample](##Examples.Ram.GraphDegree) is a concrete use of this boundary.
Its implemented operation is the [reusable array sum](##Complexity.Computability.Ram.Array.Sum).
The graph proof only identifies the represented row's list sum with mathlib's
`SimpleGraph.degree` and applies the existing function contract. It does not reprove
the traversal, register updates or unchanged-memory facts. The row is explicitly
preloaded; converting an abstract graph to that layout would need its own implementation.
Its `sum_eq_degree` theorem also states a direct equality about the ordinary executable
`ArraySum.sum`. It rewrites `ArraySum.sum_eq` and the mathematical adjacency-row sum,
without opening an execution relation or a calling-convention proof.

The array-sum source accepts `xs : array`, and `sumPair(left : array, right : array)`
calls it as `call sum(left)` and `call sum(right)`. The generated argument builders take
`Ram.ArrayRef` values; `array.Rep heapLimit xs entry` supplies the mathematical contents,
exact length and existing memory representation. `sum_function_contract_of_ref` and
`sumPair_function_contract` expose the returned list sums and unchanged shared state.
The two read-only references may overlap: this client does not need a disjointness premise.
Mutating operations still need their own aliasing and frame conditions. Passing a reference
does not prove its representation or execute a list loader. The
[array-argument sample](##Examples.Ram.ArrayArguments) uses
`sumFunctions.eval.sumPair left right heapLimit entry` for the mathematical result and
`sumFunctions.run.sumPair left right heapLimit entry` for actual compiled execution.
Its explicit heap and stack premises are separate from any time estimate; the
mathematical list concatenation does not allocate a new runtime array.

The [local-slice client](##Examples.Ram.ArraySlice) binds
`let window ← call slice(xs, offset, count);` and calls the imported sum on
the returned array reference. `slice` declares `: array` and returns
`subslice(xs, offset, count)`. `Ram.ArrayRef.Rep.subslice` supplies the ordinary
`(xs.drop offset.toNat).take count.toNat` representation;
`Ram.ArrayRef.Rep.subslice_end_lt` carries the parent's strict endpoint bound to
the selected interval. The slice contract carries the returned reference's representation
to the sum call, which reuses sum's existing contract rather than its traversal proof.
Descriptor evaluation and both returned fields are part of the compiled call, not
a host-side loader or copy. Containment, representation
and non-wrapping addresses remain explicit, and the postcondition preserves the
entire caller state, including arbitrary initial stream contents.

After `sumSlice_eq` identifies the ordinary executable result, the
[slice-properties client](##Examples.Ram.ArraySliceProperties) proves
`sumSlice_zero`, `sumSlice_whole` and `sumSlice_partition` by ordinary list reasoning.
The whole-slice result agrees with `ArraySum.sum`; the partition result adds the two
slice results modulo the word range. These proofs use the value equations and
standard `List.take`/`List.drop` identities, not execution relations, register updates
or loop proofs. The partition theorem compares returned values and does not compile
its two host applications into one program or supply their combined cost.

For a scoped `for` with one scalar expression update,
[the source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Expression)
`Ram.Source.Array.ForIn.Expression.function_contract` uses the generated body and
return equations to infer the private slots. Sum and count share its cursor progress,
termination and framing proof. The first argument is an array; additional word
parameters are retained automatically as the full `array.args ++ captures` prefix.
Count therefore needs no separate invariant to preserve its target.
The client still proves the actual expression's read safety and evaluation as the
mathematical fold step, using the supplied parameter equalities where needed.
Array representation, address range and the ordinary `List.foldl` identity also
remain mathematical obligations. The separate measured rule derives iteration
costs from compiled instructions; a host-language callback is not a free operation.
The [count client](##Examples.Ram.ArrayCount) then derives permutation invariance
directly from `List.Perm.count_eq`. It uses the typed reference contract for
`count(xs : array, target)`, with independently represented arrays that may live in
different heaps. The theorem equates returned counts, not the states or the work needed
to construct those arrays. Its `runCount_eq` theorem also covers an actual compiled
call with the target word as a runtime argument, returning the count independently
of stream output. The [sum client](##Examples.Ram.ArraySum) likewise reuses the function
contract and measured execution for its value equation and runner, without another
raw loop proof. Its ordinary `sum` application takes representation/range evidence
and a stack-capacity proof, both erased at runtime; `sum_eq` identifies the actual
returned natural number. No mathematical list is passed as executable data.
Fixed verified helper calls have their own
[source-derived rule](##Complexity.Computability.Ram.Array.ForIn.Function);
these two conveniences remain specialized scalar folds. General bodies use the
invariant rule below; short-circuiting still needs a separate language interface.

These rules operate on fixed source statements. They do not turn an arbitrary mathematical
function into executable code. See [data models](ComplexityDocs/Models.html) for array, matrix,
partial-map and framing interfaces.

## Loops and recursive calls

For a loop, choose a mathematical invariant and a well-founded progress argument.
`Ram.Source.Refines.while_wellFounded` relates the real guard and body to an abstract step
and eventual result. If a decreasing natural number is enough,
`Ram.Source.Verification.TotalWP.while_variant` provides a direct total-correctness rule.
The guard, representation and safety obligations remain at the implementation boundary.

For an arbitrary body of `Stmt.forIn`,
`Ram.Source.Verification.TotalWP.forIn` handles setup, each actual element load
and the two cursor updates. Supply an invariant at the loop head and prove the
body from `ForIn.loadedState` into an invariant after `ForIn.advanceState`.
The body must preserve the remaining count of its loaded entry state. The rule
uses ordinary natural descent, not a proposed time budget. The invariant need
not describe a single accumulator or unchanged heap: it can relate several
locals and mutable data to ordinary mathematical values.

This is an implementation-side combinator, not automatic invariant inference.
The loop-head invariant is not assumed to survive the element assignment.
Each load reads the current heap; body effects reach the next iteration.
Initialization evaluates length after assigning the pointer, and address safety
is required only when the guard is nonzero. The rule does not assert that an
arbitrary body preserves the original array contents or pointer trajectory.
See [general foreach correctness](##Complexity.Computability.Ram.Verification.ForIn).

For a forward traversal that preserves its private cursor locals, prefer
`Ram.Source.Verification.TotalWP.forIn_indexed`. Supply a payload
`invariant : Nat → State w → Prop` for the mathematical iteration number.
The rule owns the pointer/count relation, count subtraction, termination and
exit-index argument. The body proof receives `i < n` and the payload at the
pre-load state, starts at the actual current-heap element load, and establishes
the next payload after `ForIn.advanceState`. It does not assume the payload
survives loading its element local. Cursor preservation is an endpoint premise,
so writing and restoring a cursor is allowed; static destination exclusion is
one way to prove it. Memory and I/O may change. The setup equations still use
sequential expression evaluation, and only executed addresses need be safe.

If the payload is insensitive to the two private cursor locals, use
`Ram.Source.Verification.TotalWP.forIn_indexed_of_frame`. Prove once that
`State.LocalFrame {pointer, remaining}` preserves it. Then initialization starts
from the original state and the body only proves `invariant (i + 1)` at its own
endpoint; the shared rule transports this through cursor setup and advance.
Only those generated assignments use the unchanged-shared-state frame, not the
arbitrary body. Map uses this interface without unfolding `advanceState`.

The independent `Ram.Source.TimeBound.forIn` accepts a uniform conditional body
bound `B` and preservation of the remaining count on completed body executions.
It adds the actual setup expression lengths, `(B + 14) * count` and the remaining
four setup/final-guard instructions. No body totality or heap-purity premise is
needed for this conditional result. The existing helper-call traversal reuses
this rule; its separate prefix-dependent bounds remain available.
See [general foreach costs](##Complexity.Computability.Ram.Verification.Time.ForIn).

The [in-place map operation](##Complexity.Computability.Ram.Array.Map.Function)
is a mutable consumer of these rules. Its typed contract takes a borrowed array,
returns `Unit`, and produces a representation of `xs.map transform` together
with the outside-array frame and preserved I/O. The helper is a statically linked
source function, proved to implement `transform` on the original list elements.
The mathematical function is only its specification, not a runtime callback.

The [map client](##Examples.Ram.ArrayMap) uses the existing DSL:

```text
fn mapSquares(xs : array) : Unit {
  for i, x in xs {
    let y ← call Scalar.square(x);
    xs[i] := y;
  }
  return;
}
```

Its correctness proof reuses the imported square contract and the common map
theorem. Index initialization and increment are real generated assignments;
both loop bindings stay within the body. The operation proof uses the indexed
rule to maintain the ordinary
updated-prefix/unread-suffix list without its own private cursor/count invariant.
The body directly composes a function-call WP, `Ram.Source.Array.store_contract`
with its count forgotten, and an assignment WP. The continuation receives the
updated `List.set` representation and frame instead of rebuilding an execution
endpoint. It reads each original element before replacing it.
Empty arrays are admitted; an unused final pointer may wrap
at the address-space endpoint. The actual descriptor length remains word-sized.

The independent map bound is `(C + 23) * length + 8`, where `C` is the helper's
proved body bound plus its actual compiled calling overhead. It requires a
uniform conditional helper bound on one-word inputs, not helper totality.
For this imported square, the full compiled invocation has bound
`46 * xs.length + 71`; `applyState_contents` observes `List.map` from the same run.
The map changes memory, so a returned `Unit` alone is not its mathematical output.
No host list loading or allocation is included.

This is a reusable operation, not a general named-invariant elaborator or runtime
higher-order function. Arbitrary mutable bodies still use the explicit invariant
rule; input-dependent helper costs need a corresponding ordered cost proof.

For local binding adapters, `Ram.Source.State.LocalFrame writes before after`
packages unchanged memory and I/O with mathlib's
`Set.EqOn after.regs before.regs writesᶜ`. Its assignment and composition rules
let a proof carry all unaffected parameters together instead of rebuilding a
chain of individual register updates. This is an endpoint relation, not an
execution or a description of every write event. An expression still needs its
read-safety and evaluation proof, and every actual assignment keeps its cost.

Function entry initializes the entire local frame. To reason that new locals
preserve parameters, compare subsequent states with `entry.enter args`, not
with the original caller's register bank. `State.restore_eq_of_shared` uses
proved memory/input/output equalities to restore the original caller without
requiring preservation of discarded callee locals. See the
[local-frame rules](##Complexity.Computability.Ram.Source.State.Frame).

For effectful bodies, `SafeExec.regs_eq_of_not_mem_writtenRegs` instead preserves
each local outside `Stmt.writtenRegs`, without requiring an unchanged heap.
The [static local-frame rules](##Complexity.Computability.Ram.Source.Frame) use
ordinary sets and include only result destinations for calls. Map and helper-call
traversal discharge their count-preservation condition by simplifying this set,
not inspecting callee executions. Static exclusion is sufficient, not necessary;
the original semantic rule still admits writing and restoring a local.

The [named search](##Complexity.Computability.Ram.Array.Search.Function) directly
opens its generated body, proves initialization, and reuses the shared loop
contract. Its time proof follows the same source decomposition. The actual
remaining `while` determines the private local slots before their separation
is checked; no extra function-body recognizer or exported loop-scoped midpoint
is needed. The shared mathematical invariant and its initialization proof remain
explicit, so this is not general automatic invariant discovery.

For a callable recursive function, ordinary mathematical induction can prove
`Ram.Source.FunctionContract` directly. The [factorial example](##Examples.Ram.Factorial)
uses natural-number induction in `function_contract`: `ram_total_vc args entry rfl`
starts the function proof from its generated body and return equations, and
`ram_total_apply` applies the induction hypothesis at the smaller argument.
This main correctness proof does not construct a `TotalSpec`, name local registers
or prove stack-frame equations. The mathematical induction, argument-range facts
and word-arithmetic lemmas remain explicit; no time budget enters the proof.

`Ram.Source.Refines.call` can package a proved function specification as a refinement
of a call. Argument binding and return adaptation are handled at this boundary;
shared heap and I/O effects survive return, while the call theorem restores the
caller's other locals.

The API chapters on [control flow](##Complexity.Computability.Ram.Verification.Control),
[total recursion](##Complexity.Computability.Ram.Verification.Recursion.Total) and
[calls](##Complexity.Computability.Ram.Verification.Call) give the exact premises.

Use `Ram.Source.Recursion.TotalSpec` when the specification also needs the complete
callee-body endpoint. Its well-founded rules establish that stronger conclusion;
`Ram.Source.Recursion.TotalSpec.verify_wellFounded_function` presents smaller
invocations as argument/result contracts while retaining the body-state obligation.
The factorial example's separate `recursive_total` theorem instead unfolds one body
step and reuses `function_contract` to prove its local-state endpoint explicitly.
A returned value and restored caller state do not determine the callee's discarded
locals. This stronger interface is available when needed, not a prerequisite for
the function's main correctness proof. Neither route automatically chooses a
termination argument or compiles an arbitrary ordinary Lean definition.

## Stateful mathematical models

Use `StateM σ α` when a sequence of updates is easier to describe with state and a returned
value. It is an optional semantic model, not a second program every user must write.
Lean's `Std.Do.Triple` and `mvcgen` can prove its mathematical specification.
The same I/O example contains:

```lean
def incrementState : StateM (Word w) PUnit := do
  let value ← get
  set (value + 1)

open Std.Do in
theorem incrementState_spec (x : Word w) :
    ⦃fun state => ⌜state = x⌝⦄ incrementState
    ⦃⇓ _ state => ⌜state = x + 1⌝⦄ := by
  mvcgen [incrementState]
  simp_all
```

`Ram.Source.Refines.stateM_spec` transfers such a triple through a proved refinement of
`model.run`. `Ram.Source.Refines.stateM_spec_refines` keeps the native postcondition for
later operations. `Ram.Source.Refines.stateM_bind` composes returned values and state;
its mathematical continuation may depend on a returned value, but the corresponding source
statement is fixed and must obtain that value through its representation.

There are also [call](##Complexity.Computability.Ram.Verification.StateM.Call) and
[finite traversal](##Complexity.Computability.Ram.Verification.StateM.Traversal) bridges.
The call bridge represents returned fields as an ordinary list. Its register-observation
form requires distinct destinations to recover every field from the final registers;
the source call itself permits repeated destinations with last-write-wins assignment.
`mvcgen` verifies the mathematical model: it does not compile arbitrary Lean code or discharge
the model-to-memory connection. Reuse an existing bridge where one is available.
-/
