/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.State
import Complexity.Computability.Ram.Verification.Recursion.Total
import Complexity.Computability.Ram.Verification.Refinement

/-!
# Callable specifications over ordinary mathematical models

`Refines.call` uses an existing verified `TotalSpec` as a call implementation
of a pure mathematical function. Its return adapter can observe both the
returned values and the callee's shared-memory effects, while caller locals
are restored by the existing `State.leave` semantics.

The ghost argument indexes a specification, never generated source syntax:
the program, callee, destinations and argument expressions are fixed. Heap-read
safety and sufficient call depth remain obligations for represented inputs.
The rule adds no specification record or execution relation; it directly
reuses `TotalSpec.Correct.wp_call`.
-/

namespace Ram.Source.Refines

variable {α β : Type*} {Arg : Type} {program : Program} {heapLimit depth : Nat}
variable {f : Func} {spec : Recursion.TotalSpec f w Arg}
variable {fn : Nat} {dsts : List Reg} {args : List Expr}
variable {inputRep : α → State w → Prop} {outputRep : β → State w → Prop}
variable {model : α → β}

/-- A callable function contract refines its mathematical model. The `returned`
premise only translates the already-proved callee postcondition to the caller's
output representation; it need not construct or reason about an execution.
The available depth need only suffice on represented inputs. -/
theorem call (argument : α → Arg)
    (correct : ∀ x, spec.Correct program heapLimit (argument x))
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (resultCount : dsts.length = f.results.length)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ x caller, inputRep x caller →
      ∀ expr ∈ args, expr.ReadsBelow heapLimit caller.regs caller.mem)
    (pre : ∀ x caller, inputRep x caller →
      spec.pre (argument x) (caller.enter (args.map caller.eval)))
    (nesting : ∀ x caller, inputRep x caller → spec.depth (argument x) + 1 ≤ depth)
    (returned : ∀ x caller, inputRep x caller → ∀ callee,
      spec.post (argument x) (caller.enter (args.map caller.eval)) callee →
      outputRep (model x) (caller.leave callee dsts f.results)) :
    Refines program heapLimit depth (.call dsts fn args) inputRep outputRep model := by
  intro x caller represented
  exact (correct x).wp_call lookup arity resultCount frame (arguments x caller represented)
    (pre x caller represented) (nesting x caller represented) (returned x caller represented)

end Ram.Source.Refines
