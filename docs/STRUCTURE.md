# Module guide

Module paths follow subjects; declaration namespaces identify the objects being
defined. Moving a proof to a more focused file does not require renaming its
theorem. The library's public entry point is `Complexity`; reusable code should
import the smallest relevant modules instead.

## Library layers

| Directory | Responsibility |
| --- | --- |
| `Analysis/`, `Computability/Recurrence/` | Ordinary asymptotic, recurrence and amortized mathematics, independent of RAM |
| `Language/` | Typed source values, heap and execution; source contracts, representations and syntax |
| `Program/` | Fixed mathematical input/output interfaces and program specifications |
| `Computability/Ram/` | Word machine, register-level source, compiler, execution and resource proofs |
| `Computability/Ram/Compiler/Language/` | Connection from the independent typed source to the RAM backend |
| `Examples/` | Programs consuming the reusable interfaces, including their compiled guarantees |
| `docs/ComplexityDocs/` | The doc-gen4 user manual, separate from the reusable library |

The typed language does not import its RAM compiler. Mathematical observations
are proof views, not alternative implementations. The connection layer carries
their contracts to the same execution used for resource bounds.

## Frontend

`Language/Syntax.lean` is the recommended syntax import. `Syntax/Core.lean` and
`Syntax/Represented.lean` retain their import interfaces while their
implementations are organized by pass.

### Typed source emission: `Syntax/Core/`

| Modules | Responsibility |
| --- | --- |
| `Basic`, `Context` | Surface grammar, checked metadata, resolved function and lexical context |
| `Expression`, `LocalReturn`, `Normalize`, `Statement` | Operands, real completion slots, normalization and typed statement lowering |
| `Coordinates`, `Completion`, `Contract`, `Observation`, `Function` | Source-coordinate views, frames, block/function contracts and observation equations |
| `Pure`, `Range`, `Correspondence` | Optional native proof views and checked source correspondence |
| `Emission`, `Elaboration` | Declaration ordering, elaboration and registration of checked metadata |

`Emission` composes lowering and proof-generation branches; it does not provide
another evaluator. `Elaboration` is the command boundary. Helpers needed by
more than one module live in `Complexity.Language.Syntax.Core`; file-local
helpers remain private. These implementation helpers are not a second public
language interface.

### Represented preparation: `Syntax/Represented/`

| Modules | Responsibility |
| --- | --- |
| `Types`, `Imports`, `Basic` | Resolved representations, imported operations, naming and preparation data |
| `Expression`, `Calls`, `Control`, `Statements` | Prepare the actual source and an optional mathematical proof view |
| `Preparation` | Complete function preparation and order optional models by call dependencies |
| `OperationDeclarations` | Emit the real container-operation declarations used by the frontend |
| `Correspondence/Basic`, `Range`, `Relation`, `Exact`, `While` | Proof composition, actual range relations, heap-indexed correspondence, justified exact equations and mathematical while rounds |
| `Correspondence/While/Models` | Source-field mathematical observations shared by normal and completion rounds, independent of pure operation traces |
| `Correspondence/While/Completion` | Mathematical local-return contracts composed from actual guard/body effects and the existing completion rule |
| `Declarations`, `Elab` | Generate proof declarations and orchestrate source emission, proofs and registration |

Preparation and correspondence share explicit data in
`Complexity.Language.Syntax.Represented.Internal`. Failure to have a total model
does not remove the actual source program. A promised proof still has to check.
The recursive statement pass stays together because its mutually dependent
branches share one preparation invariant.

Core is below represented preparation. In particular, implementations of the
container operations import Core rather than the represented frontend that
uses them. Do not introduce a reverse import through an aggregate module.

## RAM connection

`Compiler/Language/Values.lean` collects three focused modules:

- `Values/Basic`: field expressions, read bounds and evaluation correspondence.
- `Values/Copy`: field copying, assignments and returned values.
- `Values/Buffer`: actual buffer reads, writes and slices.

Copy and buffer rules depend on the shared basics; neither needs to import
the other. Heap-operation dependencies belong to the buffer branch.

`Compiler/Language/Realization.lean` collects:

- `Realization/Basic`: successful source executions with word/depth conditions.
- `Realization/WP`: structural weakest-precondition rules.
- `Realization/Loop`: well-founded loops and reuse of existing finite executions.
- `Realization/Function`: function contracts and call composition.
- `Realization/LocalReturn`: the actual stopped guard, retaining the saved
  result's word-range requirement without evaluating the original test.

`Realization/Finite` and `Range` remain separate consumers. Importing them back
into the aggregate would obscure, and can cycle through, execution-cost
dependencies. Arena allocation/cleanup and measured simulation retain their own
modules. A complete simulation induction stays together; a file is not split
solely to meet a line limit.

`Arena/Loop/Completion` connects visible local-return contracts to readiness of
the same finite loop execution. Source completion contracts stay under
`Language/Eval/Locals/LocalReturn`; this RAM module adds only resource composition.
`Language/Eval/Locals/LocalReturn/Models` supplies consequence rules for
heap-indexed mathematical round contracts. The existing visible completion rule
still owns loop semantics and execution frames.

## Documentation

The existing `ComplexityDocs.GettingStarted` and `ComplexityDocs.Verification`
pages remain stable entry points. Getting-started topics separate the fixed
`Program` interface, direct word-RAM programming and execution. Verification
topics separate source views, represented data, lists, state contracts, loops,
compilation and direct RAM proofs. The entry modules import their topic pages
so doc-gen4 can resolve their module links.

Keep user workflows in that manual and API meaning beside declarations. The
[roadmap](ROADMAP.md) owns priorities and completion criteria; the
[language design](HIGH_LEVEL_LANGUAGE.md) owns semantic decisions. These roles
should not turn into duplicate implementation diaries.

## Extending the library

Put a change in the module that owns its invariant or proof obligation. Add a
module when there is a distinct reusable responsibility, not for each helper.
Preserve actual generated bodies, public names, import entry points and
registration order during a move. A local helper need not become public merely
because nearby declarations move.

Update `Complexity.lean` for reusable modules, and the manual entry/navigation
for new documentation topics. Check the changed modules and their existing
consumers, then build `Complexity`, `Examples` and `ComplexityDocs`. See the
[development guide](https://vvauted.github.io/Complexity/ComplexityDocs/Development.html)
for compiler and doc-gen4 commands. No additional test framework is needed for
module moves.
