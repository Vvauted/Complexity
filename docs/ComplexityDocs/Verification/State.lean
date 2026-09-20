/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.Buffer
import Examples.Language.Imports
import Examples.Language.ImportsCompiled
import Examples.Language.ImportsTraversalCompiled
import Examples.Language.Linking
import Examples.Language.Remainder
import Examples.Language.Scope
import Examples.Language.ScopeCompiled
import Examples.Language.TraversalComposition

/-!
# Mutable state, scratch scopes and calls

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

## Mutable locals and scoped scratch

Mutable bindings use ordinary Lean `do` in the generated equation. `x := value`
updates an existing local, and `x ← action` rebinds it to the result of a real
source call, read, slice or allocation. Branch joins retain outer updates;
leaving an ordinary binding drops only that binding, without reclaiming its
object. Ordinary `let` and parameters are immutable.
Copying an existing buffer handle does not copy its contents or alter the heap.

`with_scratch do ...` explicitly gives fresh objects a lexical lifetime. Its
core `Stmt.scope` reclaims the fresh suffix on a safe exit while keeping the
current contents of older objects. A `return` finishes the enclosing value block,
or the function when there is no value-block boundary. It first leaves any
intervening scratch scopes through their normal cleanup; the scratch scope
itself is not a separate return boundary.
For an output that must survive, allocate it outside the scratch scope and use
the inner buffers only temporarily. No implicit copy or freeze is performed.

For scratch scopes inside a value block, generated `body_completion_contract`
and `completion_contract` describe fallthrough and a local result using only
source-visible variables. `completion_spec` applies these contracts in `mvcgen`.
`completion_contract_of_body` closes the scope after checking the visible roots
and any local result against its entry heap. The full compiler state is restored
by an execution frame before cleanup; projecting the proof view cannot discard
an escaping root. The [nested worker](##Examples.Language.Scope) uses these
contracts. Its local-return loop uses `completion_rel_contract`: continuing
iterations preserve the invariant and decrease; a local result exits through
the actual masked guard without requiring another decrease. The proof view
hides private result slots, but mathematical source-state relations remain
explicit rather than being inferred automatically.

The safety premise `ScopeSafe initial finish control` says surviving locals
and any returned value are rooted in the entry object domain. `TotalWP.scope`
and `scope_compose` require this premise and apply the postcondition to
`finish.heap.take initial.objects.size`, not to a restored entry heap. The
native `Stmt.scope_action_spec` describes the same actual exit; a named block's
`spec` exposes its safe-body obligation. Mutable buffer cells contain only
scalars. Immutable heap nodes have explicit backward tail links, so retaining
a root's prefix also retains its chain. Node values use the entry-domain
rootedness rule, including when nested in products or options; rootedness alone
does not certify a typed complete list. `Exec.rooted_backward` preserves rooted
values and backward links together, including the tail exposed by `readNode`.
Its initial heap invariant is already supplied by the arena representation.
Node construction retains the same invariant by sharing a tail rooted in the
existing object domain, without a runtime traversal or validation check.

If the entry-root condition fails, source semantics retains the heap and reports
`regionEscape`, unless an earlier fault exists, in which case it preserves that fault.
Safe fault exits may reclaim storage but remain faults. The RAM backend certifies
safe exits only: it saves and restores the real allocator cursor, including
after an early return, without a runtime escape scanner or GC. Finite capacity
remains a separate backend premise. The [scratch consumer](##Examples.Language.Scope)
proves the actual nested/called source program using these rules and ordinary
array contents. Its [compiled theorem](##Examples.Language.ScopeCompiled) supplies
the separate physical workspace bound; exact peak-live-space analysis remains distinct.

## Compose strict native contracts

[Evaluation adequacy](##Complexity.Language.Eval.Basic) distinguishes finite
faults from absence of a finite result. The
[composition equations](##Complexity.Language.Eval.Composition) preserve lexical
scope, actual callee results and early returns. The
[continuation interface](##Complexity.Language.Eval.Continuation) derives ordinary
monadic composition from the same evaluation: `Stmt.evalWith` runs its continuation
only after a normal outcome. Return and fault bypass it; function fallthrough is
the defined `.missingReturn` error. These proved rules justify the generated
function equations, without a second interpreter or a user-supplied host algorithm.

For example, the pure helper has an ordinary mathematical equation:

```lean
theorem increment_eq (n : Nat) : Bounded.increment_model n = n + 1 := rfl
```

The [remainder example](##Examples.Language.Remainder) similarly proves
`Implementation.remainder n d = n % d` using `Nat.mod_eq_sub_div_mul`, including
divisor zero, then transfers it through the generated total source contract.

For native `Std.Do` reasoning, `open scoped Part.TotalCorrectness` activates the
[strict partial-value WP adapter](##Complexity.Control.Part). It requires an actual
returned value: divergence cannot establish a postcondition vacuously. The
[verification bridge](##Complexity.Language.Eval.Verification) proves source
`FunctionTotal` equivalent to ordinary result equations and to native `ExceptT`
Hoare triples with false fault postconditions. It reuses the standard transformer
instances; it does not make `mvcgen` prove source termination automatically.
Function preconditions take the initial heap, and postconditions relate it to
the returned value and final heap. The native triple fixes the initial heap as
a ghost rather than identifying it with the post-state. Calls retain the
callee's actual heap even on failure. The
[heap foundation](##Complexity.Language.Heap) supplies `Buffer.Contents`, whose
mathematical view is a native array; reads and writes correspond to `getElem`
and `Array.set`, retaining aliases. The
[RAM representation](##Complexity.Computability.Ram.Compiler.Language.Heap)
relates complete shared objects and their views to actual memory, preserving
the relation through successful reads and writes. Its placement is proof data,
not a runtime object table. The
[operation bridge](##Complexity.Computability.Ram.Compiler.Language.HeapOperation)
executes real dynamic load/store expressions and retains their compiler-derived
counts, without claiming runtime fault checks. The source language now accepts
borrowed-buffer length, reads, writes and relative slices; calls and compiled
execution retain their actual final heap rather than restoring the initial one.

The [buffer example](##Examples.Language.Buffer) reads an element, calls a
branching helper, writes the result and returns a slice. Its ordinary native-array
specification describes the update with `Array.set`. After rewriting the generated
function equation, native `mvcgen` composes the public `readM_spec`, `writeM_spec`
and `sliceM_spec`; the author supplies contents and bounds, not monad implementation
equations. The write rule also retains its real write equation for alias/frame
reasoning. `FunctionTotal.triple_spec` turns a supplied source function contract
into a native continuation rule without unfolding the callee. The frontend
generates `P.f_spec` to apply it with ordinary named arguments. The buffer proof
uses:

```lean
have clampSpec := Implementation.clamp_spec clamp_total
rw [Implementation.clipHead_eq]
mvcgen [clampSpec]
```

The author still supplies read/write contents and bounds. The helper's full
contract carries its initial heap, actual result and final heap; the rule does
not require that heap to be unchanged. No contract is guessed or
registered globally, and no loop invariant is automatically synthesized.

For a real effectful composition, the existing source program also declares:

```lean
def boundedMapPair (xs : Buffer Nat) (ys : Buffer Nat) (limit : Nat) : Unit := do
  boundedMap xs limit
  boundedMap ys limit
  return
```

Named `Unit` calls are ordinary statements; non-`Unit` results require an explicit
binding. The [composition proof](##Examples.Language.TraversalComposition) passes
each callee's `boundedMap_total_frame` to the generated `boundedMap_spec` with
the corresponding arguments and contents. The first frame supplies the second
call's current input; the second preserves the first result. The resulting
contract retains both `Array.map` results and all initially valid views disjoint
from both buffers. Disjoint slices of the same object are allowed. Neither
callee body nor its array invariant is unfolded in the caller proof.
The shared [contract-composition tactic](##Complexity.Language.Verification.Tactic)
continues the two explicit specifications with standard `mspec` rules, and its
[frame finish](##Complexity.Language.Heap.Tactic) supplies their routine logical
consequences:

```lean
have leftSpec := Implementation.boundedMap_spec (boundedMap_total_frame leftContents) xs limit
have rightSpec := Implementation.boundedMap_spec (boundedMap_total_frame rightContents) ys limit
rw [Implementation.boundedMapPair_eq]
source_vc [leftSpec, rightSpec]
```

Beyond the standard `Triple`/WP logical conversions, `source_vc` only simplifies
the generated `Env.head_cons`/`tail_cons` projections. Each supplied callee
specification is a separate local Aesop rule. In this example it continues the WP
inside the contracts' ordinary logical preconditions, where one `mvcgen` pass
stops. It does not infer a callee contract or loop invariant.
`buffer_frame` forwards known `Buffer.Contents` observations along supplied
`Buffer.PreservesOutside` relations, using existing `Buffer.Disjoint` facts in
either orientation. It reuses Aesop locally; it does not unfold array mathematics
or callee bodies, invent separation facts, or alter other `aesop` invocations.
Mathematical facts must be supplied separately; missing facts cause the tactic
to fail. The allocating
`Buffer.Copy.append` proof also uses it to retain the second input and compose
the final frame; fresh allocation and the `Array.append` identity are still proved
separately. Direct and imported traversal resource proofs use the same finish to
establish their second call's current input, keeping their original RAM bounds.

## Import verified source functions

Calls can name local functions or functions from explicitly imported source programs:

```lean
source_program Client importing Library, Other where
  def compute (n : Nat) : Nat := do
    let result ← Library.compute n
    let updated ← Other.update result
    return updated
```

The libraries must be previously declared `source_program` families, available
through ordinary Lean imports or earlier declarations. Qualify a library call
with the family name used in the `importing` clause. Public headers persist in
Lean's environment; arbitrary Lean functions are not accepted as implementations.
The [typed source linker](##Complexity.Language.Linking.Basic) can now combine
separately declared tables while renaming their actual internal calls. An
embedding preserves every selected signature and body, not just an assumed
callee contract. The [observation theorem](##Complexity.Language.Linking.Eval)
equates each mapped native action with its original action, including divergence,
finite faults and their final heaps. `SignatureMap.eval` hides only the proved
parameter/result-type transport; it observes the actual target function.

The [linked examples](##Examples.Language.Linking) place the existing recursive
factorial after the traversal table, relocating its self-call, and reuse the old
factorial and array-map/frame proofs directly. Neither algorithm is reimplemented
or unfolded again. The [extension rule](##Complexity.Language.Linking.Extension)
adds new bodies already typed against the combined table, allowing real calls
from the client into imported libraries. Generated `Client.f_eq` equations
replace imported invocation observations by the original library actions through
the proved embeddings. The [named clients](##Examples.Language.Imports) therefore
reuse the old factorial and two-buffer frame proofs without source ASTs or table
indices; a second client imports the first with the same interface.

For each imported family, the frontend exposes `Client.imports.Library.map`
and `Client.imports.Library.embedding`; `Library` is the spelling used in the
`importing` clause. These source declarations do not depend on RAM. The
[function-contract rule](##Complexity.Language.Linking.Verification)
`FunctionTotal.renameCalls` transfers an existing library contract through the
embedding, handling the dependent argument and return types internally.

The separate [resource rules](##Complexity.Computability.Ram.Compiler.Language.Linking.Verification)
provide `FunctionRealizable.renameCalls` and `FunctionCostBound.renameCalls`
with the same interface. They preserve word width, call-nesting capacity and
the original bound. Their [lowering correspondence](##Complexity.Computability.Ram.Compiler.Language.Linking.Lowering)
retains the actual inferred function frame and call overhead; the
[cost theorem](##Complexity.Computability.Ram.Compiler.Language.Linking.ExecutionCost)
preserves exact counts and reflects arbitrary target executions. Source
observation equality by itself would not establish these resource claims.

The [compiled client](##Examples.Language.ImportsCompiled) reuses the imported
factorial's three contracts and the existing structural tactics, without another
recursive induction. Its real halted invocation includes the extra caller's
work and call depth. Code and stack capacity still concern the complete linked
program; an unrelated imported function may have different space requirements
or heap effects. No host callbacks or trusted cost annotations replace these proofs.

Import the [connection-layer tactics](##Complexity.Computability.Ram.Compiler.Language.Linking.Tactic)
to pass the original library theorems directly:

```lean
ram_source_call using (Library.realizable contents), (Library.total_frame contents)
  via Client.imports.Library.embedding
```

On a realization goal the first theorem supplies realizability; on a cost goal
pass the original library cost bound instead. The second theorem is the source
correctness contract in both cases. The tactic transports those contracts by the
embedding and invokes the existing staged call rule. It retains the actual
returned value and final heap, then stops at the next call. It neither chooses
a contract nor substitutes the library body. The function-level
`ram_source_realize (names) using feasible, specification via embedding` and
`ram_source_cost (names) using bound via embedding` forms use the same proved
transport; ordinary parameter names may be omitted.

The [effectful client](##Examples.Language.ImportsTraversalCompiled) calls the
imported traversal twice with different contents contracts. The first frame
preserves the second input in the actual intermediate heap, so the second call
does not reuse a stale pre-state. Both array results and the outside-both frame
appear together in the compiled invocation's represented final heap. The views
may be disjoint slices of the same object. Its instruction bound reuses the
original composition bound, with imported call overhead identified by the
lowering theorem; no loop-cost or array-correctness proof is repeated.
-/
