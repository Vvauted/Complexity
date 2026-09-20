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
include scalars, arrays, products and options, observed in the actual final heap.

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
Prepared source supports field projection, construction and returned records with
array fields; natural-array `++` uses an actual allocation and copying call.
Branch results may also contain arrays: the selected branch supplies the actual
record, and a common continuation executes once. A return in such a value branch
finishes that block, not its caller; actual result-slot operations are included
in the compiled cost. Array `.size`, scalar/Boolean
conditions and direct calls to imported pure source functions use the same
source correspondence. The typed-program example combines these operations;
it does not supply a second record implementation or a private import bridge.

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
and invocation rules. `program_packing% append` reads the actual generated
packing; no second adapter is supplied. The full bound counts output allocation
and initialization, both copying calls, record-field operations, entry packing,
calls, returns and the final halt.

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
Resource proofs still explicitly compose operation certificates; general native
resource inference is separate from the automated correctness correspondence.
The shared `program_wrapper_measured` and `program_wrapper_cost` tactics now
perform the structural entry/call composition in this example from the supplied
append certificate. They follow the actual generated source, preserve its
function-table embeddings and retain every call's initialization and return cost.
Mathematical loop invariants and result-dependent operation bounds are not inferred.

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
