/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.State
import Complexity.Computability.Ram.Verification.StateM.Basic

/-!
# Native stateful function bodies used as calls

`Refines.stateM_call` turns a body refinement into a callable refinement of
the same native `StateM` model. No additional function-specification record is
needed. The body observes its return expressions and shared memory/I/O; the
bridge transports these observations across the existing calling convention
and restores every caller register outside the destinations automatically.
Returned fields are observed as an ordinary list of words. Distinct destinations
are required only to recover that whole list from the caller's final registers;
the underlying call still permits repeated destinations with ordered overwrites.

Shared observations deliberately take memory and I/O, not callee registers.
They can retain arrays, scratch space, endpoint frames and actual I/O changes
without claiming that discarded callee locals survive return. The entry ghost
appears only in representation predicates; it does not specialize the program.
Function lookup, argument and result arity, parameter-frame bounds, argument-read safety, the
entered body precondition and sufficient call depth all remain explicit.
-/

namespace Ram.Source.Refines

universe u

variable {α σ : Type u} {program : Program} {heapLimit bodyDepth depth : Nat}
variable {f : Func} {fn : Nat} {dsts : List Reg} {args : List Expr}
variable {bodyInput : σ → State w → Prop} {returnRep : α → List (Word w) → Prop}
variable {sharedRep : α × σ → (Word w → Word w) → List (Word w) → List (Word w) → Prop}
variable {model : StateM σ α}

/-- Apply a native stateful body specification at an ordinary call. The caller
receives the actual returned fields, shared-state observations and restored local
frame, ready for further native binds. Return representations may be lossy;
no inverse decoding or unchanged-memory/I/O premise is silently assumed.
Distinct destinations make each returned field observable without overwriting
an earlier field. Zero-result calls use the empty list directly. -/
theorem stateM_call
    (body : Refines program heapLimit bodyDepth f.body bodyInput
      (fun result callee =>
        (∀ expr ∈ f.results, expr.ReadsBelow heapLimit callee.regs callee.mem) ∧
        returnRep result.1 (f.results.map callee.eval) ∧
        sharedRep result callee.mem callee.input callee.outputRev) model.run)
    (entry : State w)
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (resultCount : dsts.length = f.results.length)
    (distinct : dsts.Nodup)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (nesting : bodyDepth + 1 ≤ depth) :
    Refines program heapLimit depth (.call dsts fn args)
      (fun state caller => caller = entry ∧
        bodyInput state (caller.enter (args.map caller.eval)))
      (fun result finish => returnRep result.1 (dsts.map finish.regs) ∧
        sharedRep result finish.mem finish.input finish.outputRev ∧
        ∀ r, r ∉ dsts → finish.regs r = entry.regs r)
      model.run := by
  rintro state caller ⟨same, pre⟩
  subst caller
  apply Verification.TotalWP.call (body state) lookup arity resultCount frame arguments pre nesting
  rintro callee ⟨returned, shared⟩
  have values : dsts.map (entry.leave callee dsts f.results).regs =
      f.results.map callee.eval := by
    apply List.ext_getElem
    · simpa only [List.length_map] using resultCount
    · intro i hi _
      simpa only [List.getElem_map] using
        State.leave_getElem entry callee dsts f.results distinct resultCount i
          (by simpa only [List.length_map] using hi)
  refine ⟨?_, ?_, fun r hr => State.leave_ne _ _ _ r _ hr⟩
  · simpa only [values] using returned
  · simpa only [State.leave_mem, State.leave_input, State.leave_outputRev] using shared

end Ram.Source.Refines
