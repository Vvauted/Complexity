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
continuation. The result uses `ExceptT Fault (StateT Heap Part)`, retaining the
actual final heap even on a fault, and distinguishing finite fault from divergence.

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
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    ExceptT Fault (StateT Heap Part) (Value result) := fun heap =>
  (stmt.eval program ⟨entry, heap⟩).bind (fun outcome =>
    match outcome.2 with
    | .normal => next outcome.1.locals outcome.1.heap
    | .returned value => Part.some (.ok value, outcome.1.heap)
    | .fault error => Part.some (.error error, outcome.1.heap))

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable (program : Program signatures)

/-- Normal completion of an empty statement runs the supplied continuation. -/
@[simp] theorem evalWith_skip (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.skip : Stmt signatures Γ result).evalWith program entry next = next entry := by
  funext heap
  simp only [evalWith, eval_skip, Part.bind_some]

/-- Return supplies its actual mathematical value and ignores the normal tail. -/
@[simp] theorem evalWith_ret (value : Atom Γ result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.ret value).evalWith program entry next = pure (value.eval entry) := by
  funext heap
  simp only [evalWith, eval_ret, Part.bind_some]
  all_goals rfl

/-- A primitive binding gives its actual value to the scoped body. Only normal
scope exit removes that binding before invoking the outer continuation. -/
theorem evalWith_letPrim {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.letPrim value continuation).evalWith program entry next =
      continuation.evalWith program (Env.cons (value.eval entry) entry)
        (fun finish => next finish.tail) := by
  funext heap
  simp only [evalWith, eval_letPrim, Part.bind_map, State.cons, State.tail]

/-- A checked current-heap read uses the native action and binds its actual
scalar cell. Faults bypass both the scoped body and the normal continuation. -/
theorem evalWith_read {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (continuation : Stmt signatures (kind.toTy :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.read buffer index continuation).evalWith program entry next =
      (do
        let value ← (buffer.eval entry).readM (index.eval entry)
        continuation.evalWith program (Env.cons (kind.toValue value) entry)
          (fun finish => next finish.tail)) := by
  funext heap
  change ((Stmt.read buffer index continuation).eval program ⟨entry, heap⟩).bind _ =
    ((buffer.eval entry).readM (index.eval entry) heap).bind (fun outcome =>
      ExceptT.bindCont
        (fun value => continuation.evalWith program (Env.cons (kind.toValue value) entry)
          (fun finish => next finish.tail)) outcome.1 outcome.2)
  rw [eval_read]
  cases loaded : heap.read (buffer.eval entry) (index.eval entry) <;>
    simp only [Buffer.readM, loaded, Part.bind_some, Part.bind_map, ExceptT.bindCont,
      evalWith, State.cons, State.tail]
  all_goals rfl

/-- A source write is the existing native heap action followed by normal
continuation at its actual updated heap. A failed write retains prior effects. -/
theorem evalWith_write {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.write buffer index value : Stmt signatures Γ result).evalWith program entry next =
      (do
        (buffer.eval entry).writeM (index.eval entry) (kind.ofValue (value.eval entry))
        next entry) := by
  funext heap
  change ((Stmt.write buffer index value : Stmt signatures Γ result).eval
    program ⟨entry, heap⟩).bind _ =
      ((buffer.eval entry).writeM (index.eval entry) (kind.ofValue (value.eval entry)) heap).bind
        (fun outcome => ExceptT.bindCont (fun _ : Unit => next entry) outcome.1 outcome.2)
  rw [eval_write]
  cases written : heap.write (buffer.eval entry) (index.eval entry)
      (kind.ofValue (value.eval entry)) <;>
    simp only [Buffer.writeM, written, Part.bind_some, ExceptT.bindCont]
  all_goals rfl

/-- Borrowing checked slice metadata is native action composition, not a
snapshot of the underlying object. The actual shared heap passes to the body. -/
theorem evalWith_slice {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.slice buffer offset length continuation).evalWith program entry next =
      (do
        let view ← (buffer.eval entry).sliceM (offset.eval entry) (length.eval entry)
        continuation.evalWith program (Env.cons view entry) (fun finish => next finish.tail)) := by
  funext heap
  change ((Stmt.slice buffer offset length continuation).eval program ⟨entry, heap⟩).bind _ =
    ((buffer.eval entry).sliceM (offset.eval entry) (length.eval entry) heap).bind
      (fun outcome => ExceptT.bindCont
        (fun view => continuation.evalWith program (Env.cons view entry)
          (fun finish => next finish.tail)) outcome.1 outcome.2)
  rw [eval_slice]
  cases sliced : (buffer.eval entry).slice (offset.eval entry) (length.eval entry) <;>
    simp only [Buffer.sliceM, sliced, Part.bind_some, Part.bind_map, ExceptT.bindCont,
      evalWith, State.cons, State.tail]
  all_goals rfl

/-- Sequencing composes only normal continuations; an early return or fault in
the first statement skips both the second statement and its normal tail. -/
theorem evalWith_seq (first second : Stmt signatures Γ result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.seq first second).evalWith program entry next =
      first.evalWith program entry (fun middle => second.evalWith program middle next) := by
  funext heap
  simp only [evalWith, eval_seq, Part.bind_assoc]
  apply congrArg ((first.eval program ⟨entry, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨middle, control⟩
  cases control <;> simp only [Part.bind_some]

/-- Only the selected branch is evaluated, with the same normal continuation. -/
theorem evalWith_ite (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result)
    (entry : Env Γ) (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.ite condition yes no).evalWith program entry next =
      if condition.eval entry = true then yes.evalWith program entry next
      else no.evalWith program entry next := by
  funext heap
  by_cases test : condition.eval entry = true
  · simp only [evalWith, eval_ite, if_pos test]
  · simp only [evalWith, eval_ite, if_neg test]

/-- A source call uses the actual callee action in `ExceptT`. Only a successful
callee return binds a value and runs the caller's scoped continuation. This
equation is not a simp rule, so recursive callee bodies remain opaque. -/
theorem evalWith_call (fn : Fin signatures.length) (args : Args Γ signatures[fn].params)
    (continuation : Stmt signatures (signatures[fn].result :: Γ) result) (entry : Env Γ)
    (next : Env Γ → ExceptT Fault (StateT Heap Part) (Value result)) :
    (Stmt.call fn args continuation).evalWith program entry next =
      (do
        let value ←
          (program.eval fn (args.eval entry) :
            ExceptT Fault (StateT Heap Part) (Value signatures[fn].result))
        continuation.evalWith program (Env.cons value entry) (fun finish => next finish.tail)) := by
  funext heap
  change ((Stmt.call fn args continuation).eval program ⟨entry, heap⟩).bind _ =
    (program.eval fn (args.eval entry) heap).bind (fun outcome =>
      ExceptT.bindCont
        (fun value => continuation.evalWith program (Env.cons value entry)
          (fun finish => next finish.tail)) outcome.1 outcome.2)
  rw [eval_call, Part.bind_assoc]
  apply congrArg ((program.eval fn (args.eval entry) heap).bind)
  funext outcome
  rcases outcome with ⟨returned, finalHeap⟩
  cases returned <;>
    simp only [evalWith, Part.bind_map, Part.bind_some, State.cons, State.tail,
      ExceptT.bindCont]
  all_goals rfl

end Stmt

namespace Program

/-- The existing function evaluation is its body's continuation observation
with a missing-return fault on normal fallthrough, including Unit functions. -/
theorem eval_eq_evalWith {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) (args : Env signatures[fn].params) :
    program.eval fn args =
      (program.body fn).evalWith program args (fun _ => throw Fault.missingReturn) := by
  funext heap
  unfold eval Stmt.evalWith
  rw [← Part.bind_some_eq_map]
  apply congrArg (((program.body fn).eval program ⟨args, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨finish, control⟩
  cases control <;> rfl

end Program

end Complexity.Language
