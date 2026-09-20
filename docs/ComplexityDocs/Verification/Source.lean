/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.Factorial
import Examples.Language.OptionalBuffer
import Examples.Language.OptionalBufferCompiled
import Examples.Language.Scalar
import Examples.Language.Splay.Correctness
import Examples.Language.Splay.Specification

/-!
# Source semantics and proof views

[Correctness guide](ComplexityDocs/Verification.html) · [Manual](ComplexityDocs.html)

The new [typed core](##Complexity.Language.Basic) has its own
[finite execution semantics](##Complexity.Language.Semantics), independent of RAM.
`Complexity.Language.TotalWP` has separate normal-continuation and return
postconditions; faults cannot satisfy it. `FunctionTotal` requires an actual
returned value, with no proposed instruction bound. See the
[source verification rules](##Complexity.Language.Verification).

The [named frontend](##Complexity.Language.Syntax) has one recommended declaration:
`source_program P where`. `P.f` is the actual source action; `P.f_model`, when
available, is its checked mathematical function. Function equations and state
contracts are proof views of that same program, not different source languages.
Generating a total mathematical function is not a prerequisite for accepting
a mutable or recursive source program.

The [scalar example](##Examples.Language.Scalar) uses the default declaration:

```lean
source_program Bounded where
  def increment (n : Nat) : Nat := do
    return n + 1

  def boundedIncrement (n : Nat) (limit : Nat) : Nat := do
    let mut result := limit
    let next ← increment n
    if limit ≥ next then
      result := next
    return result
```

It generates typed source bodies and executable curried Lean functions from the
same declaration. `Bounded.boundedIncrement_model n limit` has type `Nat`; its result
statement is the ordinary equality
`Bounded.boundedIncrement_model n limit = min (n + 1) limit`.
The generated `f` retains the independent source observation, and
`f_eq` exposes one source body in `ExceptT Fault (StateT Heap Part)` notation.
For this program, `f_action_eq_native` proves successful evaluation with the
mathematical result and exactly the initial heap; `f_total` supplies the
corresponding curried total source contract.
There is no second user-written implementation or manual heap conversion.
Exact unchanged-heap equations compose checked calls, conditionals and Option
branches when their result has a heap-independent encoding. A general mutable
contract need not promise an unchanged heap, and a missing exact equation does
not reject its source program.

A branch may return early while the other path continues to a later return,
including inside a typed local `do` value block. For fully modeled operations,
the mathematical proof follows that continuation only on the continuing path;
the source keeps one shared continuation and its actual selected heap. The
[allocating List consumer](##Examples.Language.LinkedList) uses this form before
folding the selected List, with the same ordinary sum equation. A loop iteration
that can either continue or return still needs a two-outcome mathematical
summary; this closed-block support does not supply one.

Normal finite ranges inside local value blocks retain their mathematical fold.
Their generated proof uses the shared local-completion range theorem, which
also describes a stored result, its final heap and the real stopped-guard step.
Generating the two-outcome model for a range body that exits its enclosing
value block remains open; the more general theorem alone does not enable it.

The [iterative factorial](##Examples.Language.Factorial) uses one range and a
mutable accumulator through the older `(pure)` compatibility naming. Its
ordinary equality with `Nat.factorial` follows from
fold/product identities; generated source correspondence supplies totality
without a second loop-termination proof. Buffer-element iteration remains
effectful because it reads the actual shared heap.

The [structured client](##Examples.Language.OptionalBuffer) uses these as actual
source values: a pure helper returns `Option (Nat × Nat)`, a library returns
`Nat × Option (Buffer Nat)`, and its importing caller matches the optional view
before reading and updating a cell. Its `bump_contract` statement uses ordinary
buffer parameters, an `Array.modify` contents relation and a frame on the real
final heap. Constructors and projections are normalized left to right; matching
exposes a payload only in the selected `some` branch. A binding such as
`let (length, present) ← Library.inspect xs` or `some (length, offset)` uses
ordinary product patterns. The expression or call is evaluated once, and its
used fields are extracted by actual compiled projections. Source correctness, imported
contracts and the [compiled result](##Examples.Language.OptionalBufferCompiled)
all concern that one declared implementation.

In default declarations, `P.f` and `P.f_eq` expose the source action and its
one-step equation, retaining actual heaps and finite faults. When a total model
exists, it supplements this interface instead of replacing the source action.
The `Part` observations remain noncomputable, while generated total mathematical
functions can be evaluated by Lean. Native execution and certified RAM instruction costs
are different runtimes; ordinary result equality assigns no execution cost.
A terminating Lean definition returning `Part α` may return `Part.none`:
constructing the action does not establish its `Part.Dom`. Nor does a defined
finite fault establish successful return. Use `FunctionTotal` or a strict native
triple for successful source termination; a host `termination_by` on action
construction alone is not that proof.

For effectful equations, the dedicated
[`source_eval` simp set](##Complexity.Language.Eval.Simp) removes transformer
administration after opening one generated `P.f_eq`. Supply actual read, write
and recursive-call equations to `simp [source_eval, ...]`; recursive function
bodies remain opaque. This preserves the real intermediate heaps and does not
turn faults into success. The [splay proof](##Examples.Language.Splay.Correctness)
combines this interface with a mathematical `Tree`, subtree-local memory frames
and one well-founded induction. Its representation supplies access bounds;
no proposed running time or RAM capacity is needed for source correctness.

State a mutable contract using standard `Std.Do` notation, rather than spelling
out the exception/state transformer and a large execution tuple. For example,
the splay theorem's conclusion is:

```lean
⦃fun heap => ⌜heap = initial ∧ Input key keys left right tree heap⌝⦄
  Implementation.splay keys left right (root tree) query
⦃⇓ result finish => ⌜Post key keys left right query tree initial result finish⌝⦄
```

Use `open scoped Std.Do Part.TotalCorrectness`. The standard `⇓` requires
successful return; it does not allow an exceptional outcome. `Input` states
the represented tree, unique node identities and actual buffer separation.
`Post` keeps the returned root, represented output tree, rotation certificate
and frame on the actual final heap. Its ordinary `Access` consequence states
inorder preservation and the search-selected root; BST order, unique identities
and complete key-array preservation have separate proved projection lemmas.
The [specification](##Examples.Language.Splay.Specification) is shared with the
RAM theorem, not a second implementation or an unchecked summary.

Every declaration also generates `P.f_contract pre post`, with the function's
ordinary curried parameters followed by the initial/final heaps. This is the
existing `FunctionTotal` contract, not another correctness interpretation.
`P.f_total_iff` proves its equivalence to actual successful evaluation.
For resource contracts, `P.f_onArgs bound` applies an ordinary parameter function
to the actual environment; `P.f_args` constructs that environment for a call.
These generated operations replace hand-written `Env.head`/`tail` chains.

Continue with [represented data](ComplexityDocs/Verification/Representations.html) or [mutable contracts](ComplexityDocs/Verification/State.html).
-/
