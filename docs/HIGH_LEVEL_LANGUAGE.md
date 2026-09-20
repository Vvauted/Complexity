# High-level language design

One program declaration should support ordinary mathematical correctness proofs
and complexity analysis of its actual compiled implementation. Function equations
and state contracts are complementary proof views, not separate languages.

Use `source_program P where` for new programs. `P.f` is its actual source action;
`P.f_model` is present when a checked total mathematical model is available.
The common entry is implemented, but control-flow combinations and invariant-only
proof ergonomics are still incomplete. The [roadmap](ROADMAP.md#active-integration-gate)
and [detailed integration checklist](design/Integration.md) distinguish completion
of individual bridges from completion of the language.

## Design documents

| Topic | Responsibility |
| --- | --- |
| [Integration](design/Integration.md) | Common-entry status, remaining control-flow obligations and acceptance checklist |
| [Frontend](design/Frontend.md) | Source syntax, normalization, scope, calls, records and ranges |
| [Verification](design/Verification.md) | Independent semantics, successful termination, mathematical contracts and Std.Do |
| [Containers](design/Containers.md) | Concrete array/list layouts, operation contracts and language/data coverage |
| [Container frontend](design/ContainerFrontend.md) | Heap-indexed mathematical views, branches and represented recursion |
| [Container resources](design/ContainerResources.md) | Actual call composition, allocation and complete invocation bounds |
| [Memory](design/Memory.md) | Aliases, rooted handles, arena initialization and scoped reclamation |
| [Backend](design/Backend.md) | Finite-word obligations, checked lowering and old-IR theorem reuse |
| [Resources](design/Resources.md) | Same-execution costs, fixed-type programs, uniform widths and space boundaries |
| [Consumers](design/Consumers.md) | Evidence from complete programs and the remaining author-facing work |

The [module guide](STRUCTURE.md) maps these responsibilities to focused imports.
The [backend design](DESIGN.md), [research report](DESIGN_RESEARCH.md) and
[literature notes](LITERATURE.md) supply background. Research motivates choices;
only the repository's statements and proofs establish its guarantees.

## The abstraction boundary

Algorithm authors write one high-level program and prove ordinary mathematical
properties of that program. They do not prove a register program, even indirectly
through a per-algorithm adapter. RAM is an implementation and cost-model backend.

There are three distinct responsibilities:

| Author | Responsibilities |
| --- | --- |
| Algorithm author | Mathematical specification, invariant, termination argument, algorithmic bounds, and genuine input/alias/range conditions |
| Language/library author | Source-level verification rules, mathematical data views, operation contracts and their composition |
| Backend author | Representation, register allocation, calling convention, lowering correctness, capacity translation and instruction accounting |

Generated register correspondence, local freshness, receiver updates, frame
restoration and function-table relocation are discharged by shared compiler
proofs. They must not become user obligations when a new loop body is written.
Unsatisfied arithmetic or representation conditions are reported at the source
operation, not as an unexplained RAM state equality.

Backend authors are first-class library users too. Removing register proofs
from algorithm-author work means developing reusable compiler proofs, not
stopping low-level proof development. Maintain register/IR and machine-level
lemmas, composition rules and automation alongside this language, with direct
proof interfaces for new lowering cases and low-level primitives. Source-cursor
navigation can improve that workflow; its metadata is neither a semantic proof
nor a prerequisite for using the low-level rules.

### Reducing proof work at the abstraction boundary

Interface work starts with the program authors can express, not with
abbreviations for a backend theorem. Ordinary product patterns and bounded
`for` loops elaborate to the existing core. A pattern evaluates its
right-hand side once; a range retains its entry-time endpoints; iteration over
a borrowed buffer reads each cell from the current heap. These are semantic
requirements, not permission to replace mutation by an entry-time snapshot.
Native finite-range correspondence is proved separately from the effectful
surface lowering and exercised by the iterative factorial. The proof-experience
work now concerns hiding local-coordinate and contract conversions, not adding
another loop semantics.

Three kinds of mechanical work belong in the library:

1. **Local bookkeeping.** Generate the lossless local views, fixed-capture
   proofs, pattern scopes and return propagation. Public block contracts take
   ordinary parameters and mathematical pre/postconditions, without asking an
   author to reconstruct `Control`, `Env` or nested output tuples.
2. **Contract composition.** The author supplies guard and body contracts
   separately. A shared loop rule passes the actual post-guard state to the
   body, retains the complete round's starting state for descent, and handles
   false guards and early returns. Heap frames follow proved operation/callee
   facts, not a global no-aliasing assumption. The generated API must be used
   by the existing traversal, not merely accompanied by an equally long
   private adapter.
3. **Backend publication.** A shared boundary connects a mathematical result
   and independent resource argument to the same actual execution. Input
   layout, output observation and word-width policy belong to that boundary,
   not to each problem's solution. Mathematical correctness must not require
   a proposed instruction budget, and a conditional cost bound alone must not
   count as successful compiled execution.

Algorithmic invariants, genuine data/range assumptions and asymptotic analysis
remain mathematical proof obligations. Their established consequences should
be available to correctness, realizability and resource reasoning at the same
program point; opening a lower-level goal must not force a second proof of the
algorithm.

The benchmark exercise is deliberately statement-only: one fixed source
implementation must meet the mathematical answer relation and a uniform
word-instruction bound. A public logarithmic input-width rule may have a fixed
implementation overhead, but not an arbitrary input-dependent admissibility
predicate selected by the candidate. Preloaded calls remain explicitly distinct
from a complete input-stream loader. The top-tree work independently develops
mathematical clusters and decomposition rules; a cluster datatype is not yet a
balanced dynamic implementation or a RAM complexity theorem.

## A typed core with independent semantics

Use a typed, first-order core language with a Lean-like programming surface.
The elaborator retains a typed program as the semantic object, then compiles it
to the existing `Ram.Source.Stmt/Func` intermediate representation.

```text
one high-level declaration
           |
       typed core
       /        \
source behavior  backend lowering + checked certificates
and source WP         |
       |         existing Stmt / Func
mathematical          |
proofs           existing verified RAM compiler
       \              |
        ----- execution and cost theorems
```

The core's execution is NOT defined as execution of its lowered RAM program.
It has values, lexical environments, function calls and an abstract heap, without
register numbers, RAM states, ABI fields or compiler call-depth parameters.

One program may have both an independent semantics and a compiled representation.
This is not maintaining two algorithms. The forbidden duplication is asking the
user to write a reference algorithm and a separate machine implementation, then
prove their correspondence for every new program.

Alternatives not selected:

- Extending source cursors over lowered WP goals alone. This improves backend
  tooling but does not supply an independent high-level meaning.
- Accepting arbitrary Lean `StateM` computations as executable primitives.
  Their types do not expose all computation, allocation or cost.
- Replacing the existing verified machine/compiler with a new backend, or
  implementing a complete compiler for arbitrary Lean terms.

The semantic boundary begins at the elaborated typed core, as ordinary Lean
reasoning begins with elaborated terms. We do not claim verification of the
text parser/elaborator itself. Generated terms and correspondence proofs are
kernel checked; a `body_eq := rfl` about the lowered term is not the required
source-to-target correspondence.

## Semantic and public-interface decisions

### Boundaries to retain

- One user-written implementation. Automatically generated views and lowerings
  are allowed; a separately maintained host algorithm is not.
- Independent source meaning, with the existing typed core and verified RAM
  chain retained. The core can describe faults and divergence without making
  every public function expose those possibilities.
- Correctness and successful termination need no proposed time budget.
  Structural recursion or a mathematical well-founded argument is compatible
  with this requirement; recursion does not require a partial public interface.
- Reuse Lean, Std, mathlib and existing library mathematics. Keep dependency
  pins and the absence of CSLib. Specifications may use arbitrary mathematics;
  executable operations need actual implementations and correspondence proofs.
- Preserve source aliasing, arithmetic meaning, actual effects and legal input
  domains. Backend limitations must be stated or discharged, not hidden.
- Costs belong to the declared implementation and selected backend, not merely
  to an extensional Lean function. Equal results do not imply equal costs.

### The current core is not the final programming interface

The intended pure-program experience includes an ordinary total Lean function
and its usual mathematical equations. An effectful implementation should expose
mathematical data contracts, not require every caller to unpack the heap monad.
This is stronger than renaming `ExceptT Fault (StateT Heap Part)`.

Two complementary approaches share the same contract and compilation layer:

| Approach | What it can genuinely improve | What it does not establish |
| --- | --- | --- |
| Generate success/result contracts, induction rules and proof views over the existing core | Removes repeated environment, outcome and contract conversion; reuses current semantics and compiler immediately | A `Part.get` projection is normally still noncomputable. If obtaining it requires the old complete correctness proof, the difficult proof has only moved. |
| Generate a total Lean definition and corresponding core from one supported source declaration | Ordinary recursion equations and mathematical proofs can become the primary interface; Lean checks the supplied structural/well-founded recursion | Requires a shared correspondence construction, including recursion. It is not permission to compile arbitrary Lean terms or hand-maintain two function bodies. |

The second is checked for the buffer-free scalar/product/option subset; the first is the primary proof
route for genuinely mutable operations, not merely a temporary workaround.
Their shared contracts carry mathematical results, actual intermediate contents,
frames and successful termination. Generate both views from one supported
declaration where applicable; do not require independently written pure and
mutable algorithms. An in-place implementation is not obtained from a persistent
one merely by identifying their results.

Before broadening that subset, retain how one supplied termination argument
feeds the generated definition and terminating core correspondence without
another author-written induction. This promises proof transport, not the absence
of internal compiler proof obligations. Pure equations and mutable invariants
must both compose with existing imports and backend proofs.

Purity also needs a real boundary. Not writing memory is insufficient: a
read-only function can return a value depending on its initial heap. Borrowed
in-place mutation remains effectful. Hiding it behind an `Array → Array` API
requires an explicit abstraction of the input contents and a proved isolation,
ownership transfer or copying policy. Any actual copying must be implemented
and charged. Do not select an empty heap and call this heap independence.

## Acceptance and unresolved implementation choices

The [roadmap](ROADMAP.md) sequences implementation and the parallel backend proof
track. This language's criterion is algorithm-author experience; the backend
track additionally evaluates how maintainers prove and change lowering cases
using reusable interfaces. Neither is measured by the number of exported tactics.

A genuinely different mutable loop must be proved using source variables,
ordinary contents and a mathematical invariant. Its helper return, branch and
store compose without any algorithm-specific register proof. Search then
exercises a different loop shape; recursive sort exercises recursion and
multiple buffers. Their compiled bounds concern these same declarations.

Fixed semantic boundaries: independent typed core, explicit executable
operations, actual shared-state behavior where used, budget-free correctness,
checked lowering, backend-derived costs and preservation of real safety
conditions. These do not fix every public function to the current heap-action
type. Extensions beyond the checked buffer-free pure frontend and abstraction of
local mutable storage still require the design and correspondence work above.

The scalar implementation now fixes typed lexical contexts, the `source_program`
spelling, one-step monadic equations and a strict scoped Part/Std.Do interpretation.
Shared cost rules and focused tactics remove some structural bookkeeping from
scalar consumers. The roadmap now separates function-definition experience,
mutable proof contracts, structured values, memory management and public resource
claims. Scalar simplification or another imported-call variant cannot finish
those capabilities. No choice may define high-level meaning through
lowering, accept manually entered instruction prices or expose register proofs
to algorithm authors.

Richer data operations and general lifetime/encapsulation interfaces remain
scheduled capabilities, not assumed consequences of the checked scoped allocator
or a mathematical view. Arbitrary Lean compilation,
general closure conversion, a new ownership calculus, bignums, a new machine
model and a full optimizer are not prerequisites for the first usable language.
