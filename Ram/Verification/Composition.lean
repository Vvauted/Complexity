/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Recursion

/-!
# Applying contracts with an explicit continuation reserve

The continuation of a proved block or call receives its actual remaining
budget. To reserve `reserve` for later work, a client need only prove the
additive inequality `blockBound + reserve ≤ fuel`. These rules derive the
remainder inequality once, without changing execution costs or requiring the
budget-dependent postcondition to be monotone.

Relational contracts retain the real entry state directly. Clients no longer
need to freeze that entry by manually converting through `RelContract.iff_entry`.
-/

namespace Ram.Source.Verification.WP

variable {w n heapLimit depth fuel reserve : Nat} {program : Program} {stmt : Stmt}
variable {P Q : State w → Prop} {R : State w → State w → Prop}
variable {bound : State w → Nat} {post : State w → Nat → Prop} {s : State w}

/-- Apply an entry-related contract while retaining the actual unused fuel. -/
theorem of_relContract (contract : RelContract n program heapLimit depth stmt P R bound)
    (pre : P s) (budget : bound s ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining,
      fuel - bound s ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel :=
  of_contract (RelContract.iff_entry.mp contract s pre) rfl budget continuation

/-- Apply an ordinary contract after reserving a chosen lower bound on the
continuation's fuel. The unspent part is not discarded or reset. -/
theorem of_contract_reserve (contract : Contract n program heapLimit depth stmt P Q bound)
    (pre : P s) (budget : bound s + reserve ≤ fuel)
    (continuation : ∀ t, Q t → ∀ remaining, reserve ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel := by
  apply of_contract contract pre (by omega)
  intro t ht remaining hr
  exact continuation t ht remaining (by omega)

/-- The same additive reserve rule for a postcondition retaining its entry.
The continuation can inspect both real endpoint states and the actual remainder. -/
theorem of_relContract_reserve
    (contract : RelContract n program heapLimit depth stmt P R bound)
    (pre : P s) (budget : bound s + reserve ≤ fuel)
    (continuation : ∀ t, R s t → ∀ remaining, reserve ≤ remaining → post t remaining) :
    WP n program heapLimit depth stmt post s fuel :=
  of_contract_reserve (RelContract.iff_entry.mp contract s pre) rfl budget continuation

end Ram.Source.Verification.WP

namespace Ram.Source.Recursion.Spec

/-- Reserve a lower bound on continuation fuel across an ordinary verified
call. The callee contract still supplies termination, memory effects and
return safety; the real setup/return overhead remains in `callBudget`. -/
theorem Correct.wp_call_reserve {w n heapLimit : Nat} {program : Program}
    {f : Func} {Arg : Type} {spec : Spec f w Arg} {arg : Arg}
    (correct : spec.Correct n program heapLimit arg)
    {fn dst depth fuel reserve : Nat} {args : List Expr} {caller : State w}
    {post : State w → Nat → Prop}
    (lookup : program[fn]? = some f) (arity : args.length = f.params)
    (frame : f.params ≤ f.locals)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit caller.regs caller.mem)
    (pre : spec.pre arg (caller.enter (args.map caller.eval)))
    (nesting : spec.depth arg + 1 ≤ depth)
    (budget : spec.callBudget n args arg + reserve ≤ fuel)
    (continuation : ∀ callee,
      spec.post arg (caller.enter (args.map caller.eval)) callee →
      ∀ remaining, reserve ≤ remaining → post (caller.leave callee dst f.result) remaining) :
    Verification.WP n program heapLimit depth (.call dst fn args) post caller fuel := by
  apply correct.wp_call lookup arity frame arguments pre nesting (by omega)
  intro callee hc remaining hr
  exact continuation callee hc remaining (by omega)

end Ram.Source.Recursion.Spec
