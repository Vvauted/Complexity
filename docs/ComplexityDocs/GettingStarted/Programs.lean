/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity
import Examples.Language.LinkedList
import Examples.Language.Program
import Examples.Language.ProgramCompiled

/-!
# Correctness-and-complexity tasks

[Getting started](ComplexityDocs/GettingStarted.html) · [Manual](ComplexityDocs.html)

The [fixed-type interface](##Complexity.Program.Basic) separates a mathematical
input/output requirement from a bound on the same compiled implementation:

```lean
def Task : Prop :=
  ∃ solve : Complexity.Program (Array Nat) Nat,
    solve.Correct isLegal (fun cards result => result = answer cards) ∧
    solve.TimeO isLegal Array.size (fun n => n + 1)
```

`solve` is a source program, not an arbitrary Lean function or a record
containing its own desired answer. `Correct` takes an ordinary input/output
relation, so a task can describe acceptable results without selecting one
reference algorithm. `TimeO` separately takes the input-size function and
growth bound. Both obligations refer to this same `solve`.

The [typed-program example](##Examples.Language.Program) selects the existing
bounded-increment declaration as `Program (Nat × Nat) Nat` with `program%`.
Its `program_correct` proof reuses the ordinary minimum equation and the
generated source contract. The same selection and proof commands work for the
record-valued declaration below. Invocation and evaluation bookkeeping remain
in the library; neither path requires another algorithm or an argument adapter.

Selection itself does not require an existing correctness proof or total pure
model. The same example selects the original effectful allocating `make` as
`Program (Nat × Nat) (Array Nat)` using `program%`. Its separately stated
correctness is the ordinary `Array.replicate` result. `Correct.of_triple` reuses
its standard `Std.Do.Triple` contract and the actual final-heap array observation;
no alternate pure implementation or pointer decoder is supplied.

The [input instances](##Complexity.Program.Input) and
[array composition](##Complexity.Program.ArrayInput) supply scalars and multiple
`Array Nat` or `Array Bool` arguments in right-associated tuples. Each array has
its own source object and physical interval; appending an input retains earlier
object identifiers and contents. Empty arrays also retain distinct identities.
The shared proof supplies initialization at every admitted word width. Results
include scalars, arrays, scalar linked lists, products and options, observed in
the actual final heap. `List Nat` and `List Bool` use immutable linked nodes,
not arrays or a free host decoder. Products and options may contain these lists;
nested lists and lists of records still need general element layouts.

[Signed inputs](##Complexity.Program.IntInput) retain ordinary `Int` and `Array Int`
at the fixed task boundary, including record fields and outputs. Scalars use
their canonical Boolean/natural constructor fields: `(true, n)` means `-(n + 1)`,
so `-1` remains distinct from zero. Arrays use two actual equal-length columns;
the [RAM input layout](##Complexity.Computability.Ram.Compiler.Language.Program.IntInput)
retains both columns, extents and width requirements.
The [integer operation contracts](##Complexity.Language.Buffer.Prod.Int) reuse
the existing pair reader and initialized allocator, proving ordinary signed
`Array.getD` and `Array.replicate` observations, including negative defaults.
`source_program` accepts signed parameters, results, literals and supported
record fields, and publishes these two real array operations at their ordinary
Lean types. Composite column reads also support signed record fields and
borrowed `Array Int` rows. The typed-program example proves their ordinary
`Array.getD` and `Array.replicate` equations using `program_correct`, without
consumer-written input-packing proofs.
The same source functions retain their existing cost certificates. This does
not yet publish general signed arithmetic syntax or infer a complete caller's
RAM readiness and time bound.

The typed-program example selects the existing linked-list constructor directly:

```lean
def singleton : Complexity.Program Nat (List Nat) :=
  program% LinkedList.NativeConstruction.singleton

theorem singleton_correct :
    singleton.Correct (fun _ => True) (fun head result => result = [head]) := by
  program_correct LinkedList.NativeConstruction.singleton using LinkedList.singleton_eq
```

The proof reuses the ordinary list equation. The returned root and its actual
allocated node satisfy the fixed output representation; this correctness theorem
does not itself supply a time bound or a fixed list-input layout.

Ordinary closed records can use standard Lean deriving:

```lean
structure AppendInput where
  left : Array Nat
  right : Array Nat
  deriving Complexity.Program.Input, Complexity.Program.RamInput

structure AppendOutput where
  values : Array Nat
  deriving Complexity.Program.Output
```

The [deriving handlers](##Complexity.Program.Deriving) generate a checked
direct-field view and reuse the same tuple interfaces; the
[RAM handler](##Complexity.Computability.Ram.Compiler.Language.Program.Deriving)
uses exactly that input layout. The existing typed-program example writes the
operation directly on those records, retaining its `(native)` compatibility naming:

```lean
source_program (native) NativeAppend where
  def append (input : AppendInput) : AppendOutput :=
    { values := input.left ++ input.right }

def append : Complexity.Program AppendInput AppendOutput :=
  program% NativeAppend.append

theorem append_correct :
    append.Correct (fun _ => True)
      (fun input output => output.values = input.left ++ input.right) := by
  program_correct NativeAppend.append using (fun input => rfl)
```

The [program selector](##Complexity.Program.Syntax) uses the registered
declaration's actual source and representation information, not an independently
selected implementation. Its
[packing entry](##Complexity.Program.Packing) assembles the fixed separate
input parameters through real product primitives and calls that function.
The source correspondence connects the native array expression to the existing
allocating copy implementation, preserving prior array observations. The
correctness proof needs only the ordinary mathematical equation; the library
handles input packing, source correspondence and the actual returned contents.

Registration is fixed by the task before choosing a candidate. It does not run
arbitrary host preprocessing or compile arbitrary Lean record operations.
Currently deriving requires nondependent direct fields, no type parameters or
inheritance, and an existing interface for the resulting ordered field tuple.
Derived records also compose as fields before later fields, including when the
nested record contains arrays. Product reassociation and the derived prefix
instances reuse the same ordered layout; no field needs to be moved to the end
just because it is a record. This is input registration, not extra runtime copying.
Prepared source supports field projection, construction and returned records with
array fields; natural-array `++` uses an actual allocation and copying call.
Branch results may also contain arrays: the selected branch supplies the actual
record, and a common continuation executes once. A return in such a value branch
finishes that block, not its caller; actual result-slot operations are included
in the compiled cost. Array `.size`, scalar/Boolean
conditions and direct calls to imported pure source functions use the same
source correspondence. The typed-program example combines these operations;
it does not supply a second record implementation or a private import bridge.

`Array Nat` and `Array Bool` also support `values.getD index fallback`, including
record receivers such as `input.values.getD index fallback`, and the fully
qualified `Array.getD values index fallback`. This calls a bounds-checking source
function: an in-bounds access reads the actual cell, and an out-of-bounds access
returns the supplied default. The mathematical proof uses ordinary `Array.getD`;
no index proof is required. Reading preserves all existing array observations,
including aliases, so a later read may reuse the same inputs. The typed-program
example combines a Boolean mask and a natural array with different possible
lengths, and proves its `Program.Correct` contract through `program_correct`.

Nested `Array (Array Nat)` and `Array (Array Bool)` inputs use the public
[row-boundary layout](##Complexity.Program.RaggedArrayInput). The same `.size`
and `.getD` expressions work: a row read executes two boundary reads and forms
a checked borrowed slice, followed by ordinary cell reads. Empty rows and
out-of-bounds fallback arrays keep their ordinary Lean meanings. The example's
`raggedLookup_correct` states only nested `Array.getD` expressions and uses
`program_correct`; it contains no descriptor arithmetic or heap decoder.
Returning a nested scalar input also uses its actual buffers at the final heap.

Rows of Nat/Bool pairs use the same expressions and one shared boundary buffer,
alongside the existing two payload columns. A row read calls the checked scalar
row operations on those columns and returns both borrowed slices; the following
pair lookup performs its actual bounds check and cell reads. Empty rows and the
complete supplied fallback row retain their ordinary meanings. The
`intervalWidth_correct` consumer states nested `Array.getD`, pair projections
and lengths, and again uses `program_correct` without a private layout adapter.

The fixed invocation layout contains all original cells, row boundaries and
their width requirements. Constructing this layout during execution is not a
free operation. Row views alias the existing payload, and arbitrary later writes
need the usual contents-preservation proof. More deeply nested arrays and
mutable nested-array construction are not provided by this two-level column layout.

Arrays of closed records compose their existing scalar and array field layouts.
For example, a record containing `tag : Nat` and `values : Array Nat` uses a
scalar column and a ragged column. Deriving `Program.Input` and `Program.RamInput`
for that element registers its array input too. Reading `readings.getD i fallback`
executes the real column operations and observes the original record; `.size`
uses the common row count. `recordLookup_correct` in the typed-program example
states ordinary record projections and nested lookup, with `program_correct`
handling the source correspondence. This does not support empty/Unit-only
record elements, arbitrary element types or arbitrary record-array mutation.
The fallback in this example is a nested record before a later scalar field;
its derived prefix layout composes with the record-array input unchanged.

Defaults containing arrays must themselves have actual represented storage.
`Array.replicate length initial` for Nat/Bool scalars or scalar pairs allocates
and initializes that storage through the existing allocator, preserving old
contents. A pair allocates both real columns and retains the first while creating
the second. At length zero the objects are still real, so an algorithm can construct a fallback record
without requiring another input array. Its model is ordinary `Array.replicate`;
allocation and initialization remain part of the compiled computation, not free
mathematical preprocessing. Composite reads preserve the heap but allocate no
replacement record storage. Whole-program resource proofs remain independent
of these source correctness and preservation contracts.

The [lookup cost module](##Complexity.Computability.Ram.Compiler.Language.Buffer.GetD)
derives input-independent bounds from the actual source body and existing
compiler rules. Its arena bounds compose conditionally with caller readiness;
these leaf bounds do not by themselves prove a complete program's `TimeO`,
word-range readiness or input-loading cost.
The [row-lookup costs](##Complexity.Computability.Ram.Compiler.Language.Buffer.Ragged.GetD)
likewise count the actual boundary reads and checked slice, independently of
the selected row's length; no payload copying is hidden in that bound.

Self-recursive functions with a checked mathematical model may carry heap-backed
values. The
[linked-list example](##Examples.Language.LinkedList) allocates one node, passes
the resulting list to its recursive call and proves the ordinary equation
`replicateAppend count head tail = List.replicate count head ++ tail`.
The same user termination hint is checked for the mathematical function and its
generated source correspondence. The latter relates values at the actual heap
after allocation; it does not identify list handles with mathematical lists.

This is not arbitrary Lean compilation or a complete persistent-array API.
The same linked-list example repeatedly appends to an array-valued record with
an actual `while` loop. Its `repeatAppend_correct` proof uses generated named
mathematical locals and `model_spec`, supplying a mathematical invariant and
well-founded descent. Generated correspondence tracks the represented fields
at each actual intermediate heap, without an author-written loop-state relation
or a total pure `while` model. The published postcondition states the resulting
copy count; it does not state an equation for the final array contents.
Non-identity observations combined with effects and local completion, nested
ranges and further control-flow combinations remain integration work. Program
selection checks the fixed input and output representations.
Source correctness alone does not supply the independent whole-program time
bound, including any added packing and call instructions.

The [compiled record example](##Examples.Language.ProgramCompiled) independently
proves `append.TimeO (fun _ => True) (fun x => x.left.size + x.right.size) (fun n => n)`.
It composes the existing array-copy cost with shared field-projection, packing
and invocation rules. The shared pass follows the actual generated body;
the consumer supplies no separate packing or import-index formulas. The full bound
counts output allocation and initialization, both copying calls, record-field
operations, entry packing, calls, returns and the final halt.

The shared [capacity rule](##Complexity.Computability.Ram.Compiler.Language.Program.Capacity)
chooses one input-independent constant for the actual code and fixed-depth stack.
For recursive programs, its
[polynomial-depth extension](##Complexity.Computability.Ram.Compiler.Language.Program.Capacity.Polynomial)
instead accepts input-dependent call depth with one uniform polynomial envelope.
`Program.TimeO.of_measured_depth_auto` uses that bound under the same width policy.
It does not discharge bounds on computed values, allocation or total execution.
The [array-input rules](##Complexity.Computability.Ram.Compiler.Language.Program.ArrayInputResources)
provide cell ranges and room for the combined output. The
[time publication rule](##Complexity.Computability.Ram.Compiler.Language.Program.Time)
combines these with the measured body at every admitted width. This example
covers all input arrays, not just inputs for which capacity was assumed.
Resource proofs still supply operation certificates and mathematical size facts;
general native resource inference is separate from automated correctness
correspondence.
The shared `program_wrapper_measured` and `program_wrapper_cost` tactics now
perform the structural entry/call composition in this example from the supplied
append certificate. They follow the actual generated source, preserve its
function-table embeddings and retain every call's initialization and return cost.
For each size, `program_wrapper_cost` can determine a uniform `Nat` budget before
introducing the input, word width and heap limit. The append consumer supplies
the existing leaf certificate and rewrites its cost using the input-size equality;
it does not write `Packing`/`Uncurry` overhead or imported-function index formulas.
Mathematical loop invariants and result-dependent operation bounds are not inferred.

The [asymptotic composition pass](##Complexity.Computability.Ram.Compiler.Language.Program.Asymptotics),
`program_time_asymptotics [leaf_BigO, one_BigO]`, combines supplied mathlib `IsBigO`
proofs through Nat addition, maxima, constant multiples, actual `callCost` and
`invocationBound`. Unfold the chosen wrapper budget first; operation budgets
remain supplied leaves. Constant absorption requires `one_BigO` proving
`(fun _ => (1 : ℝ)) =O[l] growth`, rather than assuming growth is linear.
The append example checks the inferred uniform budget and complete asymptotic
composition with its original public statement unchanged. The pass handles
cost-expression algebra, not loop/recurrence bounds, capacity or termination.

The [RAM interface](##Complexity.Computability.Ram.Compiler.Language.Program)
requires actual halted executions uniformly over all admitted word widths.
The width rule is a fixed constant multiple of logarithmic input size/value
width; capacity is established inside the execution proof, not used as a
precondition excluding inconvenient inputs. The shared `TimeO.runs_correct`
rule combines the mathematical postcondition and instruction bound on one
execution. Inputs are preloaded; an executable loader is not silently included.
Correctness remains independent of word widths and time budgets.

The
[compatibility bridge](##Complexity.Computability.Ram.Compiler.Language.Program.ArrayFunction)
preserves source correctness and actual RAM time for existing
`ArrayFunction` clients viewed as `Program (Array Nat) Nat`; it does not require
another algorithm proof.
-/
