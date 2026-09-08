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
needed. The body observes its return expression and shared memory/I/O; the
bridge transports these observations across the existing calling convention
and restores every caller register except the destination automatically.

Shared observations deliberately take memory and I/O, not callee registers.
They can retain arrays, scratch space, endpoint frames and actual I/O changes
without claiming that discarded callee locals survive return. The entry ghost
appears only in representation predicates; it does not specialize the program.
Function lookup, arity, parameter-frame bounds, argument-read safety, the
entered body precondition and sufficient call depth all remain explicit.
-/

namespace Ram.Source.Refines

universe u

variable {α σ : Type u} {program : Program} {heapLimit bodyDepth depth : Nat}
variable {f : Func} {fn dst : Nat} {args : List Expr}
variable {bodyInput : σ → State w → Prop} {returnRep : α → Word w → Prop}
variable {sharedRep : α × σ → (Word w → Word w) → List (Word w) → List (Word w) → Prop}
variable {model : StateM σ α}

/-- Apply a native stateful body specification at an ordinary call. The caller
receives the actual return value, shared-state observations and restored local
frame, ready for further native binds. Return representations may be lossy;
no inverse decoding or unchanged-memory/I/O premise is silently assumed. -/
theorem stateM_call
    (body : Refines program heapLimit bodyDepth f.body bodyInput
      (fun result callee => f.result.ReadsBelow heapLimit callee.regs callee.mem ∧
        returnRep result.1 (callee.eval f.result) ∧
        sharedRep result callee.mem callee.input callee.outputRev) model.run)
    (entry : State w)
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (nesting : bodyDepth + 1 ≤ depth) :
    Refines program heapLimit depth (.call dst fn args)
      (fun state caller => caller = entry ∧
        bodyInput state (caller.enter (args.map caller.eval)))
      (fun result finish => returnRep result.1 (finish.regs dst) ∧
        sharedRep result finish.mem finish.input finish.outputRev ∧
        ∀ r, r ≠ dst → finish.regs r = entry.regs r)
      model.run := by
  rintro state caller ⟨same, pre⟩
  subst caller
  apply Verification.TotalWP.call (body state) lookup arity frame arguments pre nesting
  rintro callee ⟨returned, shared⟩
  exact ⟨by simpa only [State.leave_dst] using returned, shared,
    fun r hr => State.leave_ne _ _ _ r _ hr⟩

end Ram.Source.Refines
