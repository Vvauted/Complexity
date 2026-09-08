# Design

The [roadmap](ROADMAP.md) sets development priorities.
This note records the decisions those changes should preserve.
The [backend manual](https://vvauted.github.io/Complexity/ComplexityDocs/Backend.html)
describes the current machine and compiler interfaces.

## One program, several proof views

The executable source is a fixed first-order program, with structured control
flow, named functions and recursive calls. The existing compiler lowers it to
word-RAM instructions. Improving the proof interface should reuse that source
and compilation chain, not introduce a second independently maintained program.

Intermediate functions are the primary programming interface. Their arguments,
return values and shared-data effects must be available without a stream-based
`main`. Reading and writing external input belong to an optional outer driver.
Parameter binding and result observations are derived from the same source
declaration, not restated by each caller. Named declarations generate `eval`,
`bodyTime` and `run` entries with the declared typed parameters, followed by heap
capacity and caller state. They reuse the existing semantics and runner; they do
not fill in a reference result, a cost formula or a correctness proof.

The generic execution state retains input and output fields because functions
may have effects. Merely carrying those fields does not execute stream operations.
A pure function's contract must establish independence from their initial contents
and preservation on return; selecting an empty stream alone would not prove this.

A functional specification may be a relation, an ordinary Lean function or a
native `StateM` computation. These are proof views. A sorting specification need
not implement another sorting algorithm, and a loop need not be translated into
a total pure function before its termination can be proved.

Representation predicates relate mathematical values to visible machine state.
Use mathlib equivalences when information is preserved, and relations when a
view forgets information. An entire heap is not in bijection with one observed
list. Mathematical functions used in specifications are not executable primitives.

## Behavior first, cost second

Safe total correctness establishes an actual terminating execution without a
proposed time bound. A separate conditional time theorem bounds that execution.
Publishing and composing reusable implementations should preserve this separation.

The returned value and execution count are observations of the program, not
fields filled in by its correctness proof. Specifications and asymptotic bounds
describe those observations. An ordinary functional view must therefore come
with its connection to that implementation; declaring a mathematical reference
function alone does not make it the executable program.

`Func.eval` and `Func.bodyTime` provide proof-level observations using mathlib's
`Part`. Their domains come from safe executions, and determinism proves that
the observed result and count belong to the same invocation. Classical choice
selects only that uniquely determined observation. It does not install a
reference algorithm or a proposed cost as the program's meaning. These views
are noncomputable; executable application remains on the verified runtime path.
Heap capacity can affect the domain, and shared entry state cannot be hidden
without proving the relevant result and cost independence.

The executable function adapter uses the existing compiler and machine runner.
It places runtime arguments in parameter registers, launches a fixed call-and-halt
sequence and returns the value separately from stream output. Preloading shared
state is explicit; no loader or host-side data conversion is silently included.
The measured call includes argument evaluation, frame handling, the body, return
and halt. `Function.runUntil` has no operational limit and uses the existing
machine step until a stopping state; `Function.run` retains a limit for exploration.
Both relate to the same finite traces. The unbounded runner's logical bottom is
not an executable divergence test. Source shared memory is related only to visible
target heap cells, not to the private stack left behind by the call.

An `array` parameter is a typed by-value pair of words, not a newly allocated
descriptor. Its base and length are passed by the same call compiler as scalar
arguments. `ArrayRef.Rep` relates existing heap contents to a list; changing this
mathematical view or forming host-side subarray metadata performs no RAM copy.
Array construction inside a program must eventually have its own implementation
and cost, not be smuggled into that representation predicate.

Heap and call-depth capacities are safety premises, not instruction budgets.
Output-size guarantees support subsequent operations. Time analysis may reuse
these facts and functional invariants, but correctness must not depend on the
particular time estimate chosen later.

The source language does not accept a pricing table, arbitrary host-language
callbacks or unchecked ticks. Operation costs come from proved executions of
emitted instructions, including argument evaluation, frame save/restore and
control-flow overhead.

The read-only array fold shares one cursor, termination and framing proof for
expression updates and fixed function calls. A call-based step uses a contract
of the actual callee to establish its mathematical `List.foldl` update and
unchanged shared state. Its separate exact-count rule adds the real call and
loop instructions to a proved constant callee-body count. This does not make
ordinary Lean callbacks executable or provide a data-dependent fold-cost rule.

Scoped `for x in xs` lowers to the same statements: two fresh cursor locals copy
the descriptor, and a third local receives each actual element load. The source
element binding is immutable and does not escape the body. Generated control
code leaves the original descriptor alone; array contents are read at each
visit, not snapshotted. The generic AST helper retains its actual sequential
evaluation order, while frontend freshness makes the copied descriptor stable.
All copies, bindings and enlarged call frames retain their compiler-derived cost.
For the single-array scalar-call pattern, a function rule reads the body/result
equations to infer those slots, reusing the same traversal and callee contract.

## The current machine model

Words and addresses are finite bit vectors. Arithmetic has the specified modular
semantics; exact natural-number arithmetic requires no-overflow hypotheses.
Multiplication and division are primitives of this word-RAM model.

One executed transition costs one step. This is neither the runtime of the Lean
interpreter nor a claim about bit complexity. The optimized runner has a
correspondence theorem with the reference execution.

Address-space capacity, cumulative accessed addresses and peak live storage are
different resources. A new space claim needs its own observation of the same
execution, including allocation or reclamation if it refers to live heap.

## Complete claims

A problem fixes its encoding, admissible inputs, width policy and size measure
before an implementation is certified. Composition must preserve that original
domain and the actual intermediate representation.

Reading, initializing or converting data is runtime work when the implementation
performs it. A proof-only change of mathematical view is not a data conversion.
Preloaded-memory contracts state their entry state explicitly.

The compiler, representation and cost theorems connect to one fixed program
uniformly over legal inputs. Cross-model complexity claims additionally need a
costed simulation; payload-size arithmetic alone is not one.

## Reuse and scope

Reuse Lean, Std and mathlib definitions and theorems. Keep their pinned versions
consistent, and extend ordinary mathematical namespaces for generic results.
Backend-specific statements stay under the RAM topic.

The [literature notes](LITERATURE.md) explain the sources behind these choices.
They motivate the design; the guarantees are the theorems in this repository.
