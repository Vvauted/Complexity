/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Composition

/-!
# Source equations with normal continuations

`Stmt.evalWith` observes the existing statement evaluation and runs its supplied
continuation only on normal completion. Actual returns and faults bypass that
continuation. The result uses the existing `ExceptT Fault Part` monad, retaining
the distinction between a finite fault and divergence.

The equations below follow from the existing evaluation composition laws and
mathlib's partial-value monad laws. They neither define another interpreter nor
reprove source execution. In particular, a call uses the selected function's
existing semantic result through genuine monadic bind; its body stays opaque.
-/

namespace Complexity.Language

namespace Stmt

/-- Interpret the existing statement outcome with a normal continuation. A
returned value or fault exits immediately without evaluating `next`. -/
noncomputable def evalWith {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (stmt : Stmt signatures Γ result) (program : Program signatures) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) : ExceptT Fault Part (Value result) :=
  (stmt.eval program entry).bind (fun outcome =>
    match outcome.2 with
    | .normal => next outcome.1
    | .returned value => Part.some (.ok value)
    | .fault error => Part.some (.error error))

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable (program : Program signatures)

/-- Normal completion of an empty statement runs the supplied continuation. -/
@[simp] theorem evalWith_skip (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.skip : Stmt signatures Γ result).evalWith program entry next = next entry := by
  simp only [evalWith, eval_skip, Part.bind_some]

/-- Return supplies its actual mathematical value and ignores the normal tail. -/
@[simp] theorem evalWith_ret (value : Atom Γ result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.ret value).evalWith program entry next = pure (value.eval entry) := by
  simp only [evalWith, eval_ret, Part.bind_some]
  all_goals rfl

/-- A primitive binding gives its actual value to the scoped body. Only normal
scope exit removes that binding before invoking the outer continuation. -/
theorem evalWith_letPrim {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.letPrim value continuation).evalWith program entry next =
      continuation.evalWith program (Env.cons (value.eval entry) entry)
        (fun finish => next finish.tail) := by
  simp only [evalWith, eval_letPrim, Part.bind_map]

/-- Sequencing composes only normal continuations; an early return or fault in
the first statement skips both the second statement and its normal tail. -/
theorem evalWith_seq (first second : Stmt signatures Γ result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.seq first second).evalWith program entry next =
      first.evalWith program entry (fun middle => second.evalWith program middle next) := by
  simp only [evalWith, eval_seq, Part.bind_assoc]
  apply congrArg ((first.eval program entry).bind)
  funext outcome
  rcases outcome with ⟨middle, control⟩
  cases control <;> simp only [Part.bind_some]

/-- Only the selected branch is evaluated, with the same normal continuation. -/
theorem evalWith_ite (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result)
    (entry : Env Γ) (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.ite condition yes no).evalWith program entry next =
      if condition.eval entry = true then yes.evalWith program entry next
      else no.evalWith program entry next := by
  by_cases test : condition.eval entry = true
  · simp only [evalWith, eval_ite, if_pos test]
  · simp only [evalWith, eval_ite, if_neg test]

/-- A source call uses the actual callee action in `ExceptT`. Only a successful
callee return binds a value and runs the caller's scoped continuation. This
equation is not a simp rule, so recursive callee bodies remain opaque. -/
theorem evalWith_call (fn : Fin signatures.length) (args : Args Γ signatures[fn].params)
    (continuation : Stmt signatures (signatures[fn].result :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault Part (Value result)) :
    (Stmt.call fn args continuation).evalWith program entry next =
      (do
        let value ←
          (program.eval fn (args.eval entry) : ExceptT Fault Part (Value signatures[fn].result))
        continuation.evalWith program (Env.cons value entry) (fun finish => next finish.tail)) := by
  change ((Stmt.call fn args continuation).eval program entry).bind _ =
    (program.eval fn (args.eval entry)).bind
      (ExceptT.bindCont (fun value =>
        continuation.evalWith program (Env.cons value entry) (fun finish => next finish.tail)))
  rw [eval_call, Part.bind_assoc]
  apply congrArg ((program.eval fn (args.eval entry)).bind)
  funext returned
  cases returned <;> simp only [ExceptT.bindCont, evalWith, Part.bind_map, Part.bind_some]
  all_goals rfl

end Stmt

namespace Program

/-- The existing function evaluation is its body's continuation observation
with a missing-return fault on normal fallthrough, including Unit functions. -/
theorem eval_eq_evalWith {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) (args : Env signatures[fn].params) :
    program.eval fn args =
      (program.body fn).evalWith program args (fun _ => Part.some (.error .missingReturn)) := by
  unfold eval Stmt.evalWith
  rw [← Part.bind_some_eq_map]
  apply congrArg (((program.body fn).eval program args).bind)
  funext outcome
  rcases outcome with ⟨finish, control⟩
  cases control <;> rfl

end Program

end Complexity.Language
