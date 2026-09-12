/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Eval.Locals
import Complexity.Language.Eval.Composition
import Complexity.Language.Eval.Node.Verification
import Mathlib.Logic.Equiv.Prod

/-!
# Composition in ordinary local coordinates

These equations transport the existing source evaluation laws through
`Stmt.observe`. They expose ordinary local values and the native shared-heap
action without introducing another interpreter. Normal completion passes the
actual locals to the next block; returns and faults bypass it. Leaving a lexical
scope removes only its added binding, retaining changes to outer locals and heap.
-/

namespace Complexity.Language.Stmt

variable {signatures : List Signature} {Γ : List Ty} {result : Ty} {Locals : Type}
variable (view : Env Γ ≃ Locals) (program : Program signatures)

/-- An empty block preserves its ordinary local values and the shared heap. -/
@[simp] theorem observe_skip (locals : Locals) :
    observe view (.skip : Stmt signatures Γ result) program locals = pure (.normal, locals) := by
  funext heap
  simp only [observe, action, eval_skip, Part.map_some, Prod.swap, Equiv.apply_symm_apply]
  all_goals rfl

/-- Assignment returns the actual updated locals; it does not change the heap. -/
@[simp] theorem observe_assign {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ)
    (locals : Locals) :
    observe view (.assign target value : Stmt signatures Γ result) program locals =
      pure (.normal, view ((view.symm locals).set target (value.eval (view.symm locals)))) := by
  funext heap
  simp only [observe, action, eval_assign, Part.map_some, Prod.swap, State.set]
  all_goals rfl

/-- Return retains the current locals as well as the actual returned value. -/
@[simp] theorem observe_ret (value : Atom Γ result) (locals : Locals) :
    observe view (.ret value) program locals =
      pure (.returned (value.eval (view.symm locals)), locals) := by
  funext heap
  simp only [observe, action, eval_ret, Part.map_some, Prod.swap, Equiv.apply_symm_apply]
  all_goals rfl

/-- Only normal completion runs the next block, using the actual modified
locals and shared heap. Returns and faults keep that same completed state. -/
theorem observe_seq (first second : Stmt signatures Γ result) (locals : Locals) :
    observe view (.seq first second) program locals = (do
      let (control, middle) ← observe view first program locals
      match control with
      | .normal => observe view second program middle
      | .returned value => pure (.returned value, middle)
      | .fault error => pure (.fault error, middle)) := by
  funext heap
  simp only [observe, action, eval_seq, Prod.swap, Bind.bind, Pure.pure, StateT.bind,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((first.eval program ⟨view.symm locals, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨middleLocals, middleHeap⟩, control⟩
  cases control <;>
    simp only [observe, action, Prod.swap, Equiv.symm_apply_apply, StateT.pure,
      ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  all_goals rfl

/-- The source condition selects a block in the same ordinary local coordinates. -/
theorem observe_ite (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result)
    (locals : Locals) :
    observe view (.ite condition yes no) program locals =
      if condition.eval (view.symm locals) = true then observe view yes program locals
      else observe view no program locals := by
  funext heap
  by_cases test : condition.eval (view.symm locals) = true
  · simp only [observe, action, eval_ite, if_pos test]
  · simp only [observe, action, eval_ite, if_neg test]

/-- Match an actual optional value in ordinary local coordinates. The `some`
branch receives its payload alongside the outer locals; every exit drops only
that payload binding and preserves the actual outer locals, heap and control. -/
theorem observe_matchOption {τ : Ty} (value : Atom Γ (.option τ))
    (noneBranch : Stmt signatures Γ result)
    (someBranch : Stmt signatures (τ :: Γ) result) (locals : Locals) :
    observe view (.matchOption value noneBranch someBranch) program locals =
      (match value.eval (view.symm locals) with
      | none => observe view noneBranch program locals
      | some payload => do
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) someBranch
              program (payload, locals)
          pure (control, scopedValues.2)) := by
  funext heap
  cases selected : value.eval (view.symm locals) with
  | none =>
      simp only [observe, action, eval_matchOption, selected]
  | some payload =>
      simp only [observe, action, eval_matchOption, selected, Prod.swap,
        Bind.bind, Pure.pure, StateT.bind,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
        Equiv.prodCongr_symm,
        Env.equivProd_apply, Env.equivProd_symm_apply, State.cons, State.tail,
        ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
      apply congrArg ((someBranch.eval program
        ⟨Env.cons payload (view.symm locals), heap⟩).bind)
      funext outcome
      rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
      rfl

/-- A scoped binding is an ordinary value paired with the outer locals. On
every exit, only that binding is dropped from the actual final local values. -/
theorem observe_letPrim {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) (locals : Locals) :
    observe view (.letPrim value continuation) program locals = (do
      let (control, scopedValues) ←
        observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
          program (value.eval (view.symm locals), locals)
      pure (control, scopedValues.2)) := by
  funext heap
  simp only [observe, action, eval_letPrim, Prod.swap, Bind.bind, Pure.pure, StateT.bind,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm,
    Env.equivProd_apply, Env.equivProd_symm_apply, State.cons, State.tail,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((continuation.eval program
    ⟨Env.cons (value.eval (view.symm locals)) (view.symm locals), heap⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
  rfl

/-- Allocation runs the actual native heap action before entering its scoped
body in ordinary local coordinates. Every exit drops only the new binding and
retains the body's final heap, including allocation followed by a fault. -/
theorem observe_alloc {kind : CellTy} (length : Atom Γ .nat)
    (initial : Atom Γ kind.toTy)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) (locals : Locals) :
    observe view (.alloc length initial continuation) program locals = (do
      let allocated ← (Buffer.allocM (length.eval (view.symm locals))
        (kind.ofValue (initial.eval (view.symm locals)))).run
      match allocated with
      | .ok buffer =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program (buffer, locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_alloc, Prod.swap, Buffer.allocM, ExceptT.run,
    Bind.bind, Pure.pure, StateT.bind,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm,
    State.cons, State.tail,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((continuation.eval program
    ⟨Env.cons (heap.alloc (length.eval (view.symm locals))
      (kind.ofValue (initial.eval (view.symm locals)))).1 (view.symm locals),
      (heap.alloc (length.eval (view.symm locals))
        (kind.ofValue (initial.eval (view.symm locals)))).2⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
  rfl

/-- Node construction exposes the existing native heap action in ordinary
local coordinates. The scoped body receives the actual fresh reference; every
exit keeps its final heap and drops only that reference's lexical binding. -/
theorem observe_consNode {kind : CellTy} (head : Atom Γ kind.toTy)
    (tail : Atom Γ (.option (.node kind)))
    (continuation : Stmt signatures (.node kind :: Γ) result) (locals : Locals) :
    observe view (.consNode head tail continuation) program locals = (do
      let allocated ← (NodeRef.consM (kind.ofValue (head.eval (view.symm locals)))
        (tail.eval (view.symm locals))).run
      match allocated with
      | .ok ref =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program (ref, locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_consNode, Prod.swap, NodeRef.consM, ExceptT.run,
    Bind.bind, Pure.pure, StateT.bind,
    Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm,
    State.cons, State.tail,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((continuation.eval program
    ⟨Env.cons (heap.cons (kind.ofValue (head.eval (view.symm locals)))
      (tail.eval (view.symm locals))).1 (view.symm locals),
      (heap.cons (kind.ofValue (head.eval (view.symm locals)))
        (tail.eval (view.symm locals))).2⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
  rfl

/-- Allocation-scope exit retains all actual ordinary locals and applies the
same root check to their complete source environment. The returned control is
not caught: the surrounding observation still distinguishes return from normal
completion, and a failed scope retains the full heap with its fault. -/
theorem observe_scope (body : Stmt signatures Γ result) (locals : Locals) :
    observe view (.scope body) program locals = fun heap =>
      (observe view body program locals heap).map (fun outcome =>
        let exited := scopeExit heap (⟨view.symm outcome.1.2, outcome.2⟩, outcome.1.1)
        ((exited.2, view exited.1.locals), exited.1.heap)) := by
  funext heap
  simp only [observe, action, eval_scope, ← Part.bind_some_eq_map,
    Part.bind_assoc, Part.bind_some]
  apply congrArg ((body.eval program ⟨view.symm locals, heap⟩).bind)
  funext outcome
  rcases outcome with ⟨⟨finalLocals, finalHeap⟩, control⟩
  simp only [Prod.swap, Equiv.symm_apply_apply]

open scoped Part.TotalCorrectness in
/-- Compose the body's native weakest precondition with the actual scope exit.
The complete local environment is reconstructed only to check its roots; the
postcondition sees ordinary locals and the actual retained or unreclaimed heap.
Finite faults remain available to an arbitrary native postcondition. -/
@[spec] theorem observe_scope_spec (body : Stmt signatures Γ result) (locals : Locals)
    (post : Std.Do.PostCond (Control result × Locals) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.scope body) program locals)
      (fun heap =>
        ((Std.Do.WP.wp (observe view body program locals)).apply
          (fun outcome finish =>
            let exited := scopeExit heap (⟨view.symm outcome.2, finish⟩, outcome.1)
            post.1 (exited.2, view exited.1.locals) exited.1.heap, ⟨⟩)) heap)
      post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro heap ⟨⟨⟨control, finalLocals⟩, finalHeap⟩, execution, property⟩
  let exited := scopeExit heap (⟨view.symm finalLocals, finalHeap⟩, control)
  refine ⟨((exited.2, view exited.1.locals), exited.1.heap), ?_, property⟩
  rw [observe_scope]
  exact Part.mem_map_iff _ |>.mpr
    ⟨((control, finalLocals), finalHeap), execution, rfl⟩

open scoped Part.TotalCorrectness in
/-- A non-escaping body preserves its actual control and ordinary locals while
reclaiming only its fresh heap suffix. The author supplies the lifetime fact and
the desired postcondition on current retained contents, without opening the
scope-outcome conversion. This does not assume the body is free of faults. -/
theorem observe_scope_safe_spec (body : Stmt signatures Γ result) (locals : Locals)
    (post : Std.Do.PostCond (Control result × Locals) (.arg Heap .pure)) :
    Std.Do.Triple (m := StateT Heap Part) (ps := .arg Heap .pure)
      (observe view (.scope body) program locals)
      (fun heap =>
        ((Std.Do.WP.wp (observe view body program locals)).apply
          (fun outcome finish => ⟨
            ScopeSafe heap ⟨view.symm outcome.2, finish⟩ outcome.1 ∧
              (post.1 outcome (finish.take heap.objects.size)).down⟩, ⟨⟩)) heap)
      post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro heap ⟨⟨⟨control, finalLocals⟩, finalHeap⟩, execution, safe, property⟩
  refine ⟨((control, finalLocals), finalHeap.take heap.objects.size), ?_, property⟩
  exact mem_observe_iff.mpr (.scope (mem_observe_iff.mp execution) safe)

/-- A read uses the actual native heap action, then binds its cell in ordinary
local coordinates. A failed read skips the continuation without rolling back. -/
theorem observe_read {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (continuation : Stmt signatures (kind.toTy :: Γ) result) (locals : Locals) :
    observe view (.read buffer index continuation) program locals = (do
      let loaded ← ((buffer.eval (view.symm locals)).readM
        (index.eval (view.symm locals))).run
      match loaded with
      | .ok value =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program (kind.toValue value, locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_read]
  cases loaded : heap.read (buffer.eval (view.symm locals)) (index.eval (view.symm locals)) with
  | ok value =>
      simp only [observe, action, Prod.swap, Buffer.readM, ExceptT.run, loaded,
        Bind.bind, Pure.pure, StateT.bind,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
        Equiv.prodCongr_symm,
        Env.equivProd_apply, Env.equivProd_symm_apply, State.cons, State.tail,
        ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
      apply congrArg ((continuation.eval program
        ⟨Env.cons (kind.toValue value) (view.symm locals), heap⟩).bind)
      funext outcome
      rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
      rfl
  | error error =>
      simp only [Buffer.readM, ExceptT.run, loaded, Bind.bind, Pure.pure, StateT.bind,
        StateT.pure, Part.bind_some, Part.map_some, Prod.swap, Equiv.apply_symm_apply]

/-- One actual node read binds the stored head and shared tail in ordinary
local coordinates. Failure keeps the current locals and heap and skips the
body; successful scope exit removes only the pair's lexical binding. -/
theorem observe_readNode {kind : CellTy} (ref : Atom Γ (.node kind))
    (continuation : Stmt signatures (.prod kind.toTy (.option (.node kind)) :: Γ) result)
    (locals : Locals) :
    observe view (.readNode ref continuation) program locals = (do
      let loaded ← ((ref.eval (view.symm locals)).readM).run
      match loaded with
      | .ok contents =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program ((kind.toValue contents.1, contents.2), locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_readNode]
  cases found : heap.node? kind (ref.eval (view.symm locals)).object with
  | some contents =>
      rcases contents with ⟨head, tail⟩
      simp only [observe, action, Prod.swap, NodeRef.readM, ExceptT.run, found,
        Bind.bind, Pure.pure, StateT.bind,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
        Equiv.prodCongr_symm,
        State.cons, State.tail,
        ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
      apply congrArg ((continuation.eval program
        ⟨Env.cons (kind.toValue head, tail) (view.symm locals), heap⟩).bind)
      funext outcome
      rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
      rfl
  | none =>
      simp only [NodeRef.readM, ExceptT.run, found, Bind.bind, Pure.pure, StateT.bind,
        StateT.pure, Part.bind_some, Part.map_some, Prod.swap, Equiv.apply_symm_apply]

/-- A write observes the native action's actual updated heap. Both success and
failure retain the current caller locals; failure does not restore an older heap. -/
theorem observe_write {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) (locals : Locals) :
    observe view (.write buffer index value : Stmt signatures Γ result) program locals = (do
      let written ← ((buffer.eval (view.symm locals)).writeM
        (index.eval (view.symm locals)) (kind.ofValue (value.eval (view.symm locals)))).run
      match written with
      | .ok _ => pure (.normal, locals)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_write]
  cases written : heap.write (buffer.eval (view.symm locals)) (index.eval (view.symm locals))
      (kind.ofValue (value.eval (view.symm locals))) <;>
    simp only [Buffer.writeM, ExceptT.run, written, Bind.bind, Pure.pure, StateT.bind,
      StateT.pure, Part.bind_some, Part.map_some, Prod.swap, Equiv.apply_symm_apply]

/-- A checked slice binds metadata for the same shared object. Leaving the
binding preserves outer-local changes and every actual control outcome. -/
theorem observe_slice {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) (locals : Locals) :
    observe view (.slice buffer offset length continuation) program locals = (do
      let sliced ← ((buffer.eval (view.symm locals)).sliceM
        (offset.eval (view.symm locals)) (length.eval (view.symm locals))).run
      match sliced with
      | .ok value =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program (value, locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_slice]
  cases sliced : (buffer.eval (view.symm locals)).slice
      (offset.eval (view.symm locals)) (length.eval (view.symm locals)) with
  | ok value =>
      simp only [observe, action, Prod.swap, Buffer.sliceM, ExceptT.run, sliced,
        Bind.bind, Pure.pure, StateT.bind,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
        Equiv.prodCongr_symm, State.cons, State.tail,
        ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
      apply congrArg ((continuation.eval program
        ⟨Env.cons value (view.symm locals), heap⟩).bind)
      funext outcome
      rcases outcome with ⟨⟨scopedLocals, finalHeap⟩, control⟩
      rfl
  | error error =>
      simp only [Buffer.sliceM, ExceptT.run, sliced, Bind.bind, Pure.pure, StateT.bind,
        StateT.pure, Part.bind_some, Part.map_some, Prod.swap, Equiv.apply_symm_apply]

/-- A call binds the selected function's actual result and final shared heap.
The callee remains opaque; even a callee fault retains its heap effects while
preserving the caller's locals and skipping the continuation. -/
theorem observe_call (fn : Fin signatures.length) (args : Args Γ signatures[fn].params)
    (continuation : Stmt signatures (signatures[fn].result :: Γ) result) (locals : Locals) :
    observe view (.call fn args continuation) program locals = (do
      let returned ← (program.eval fn (args.eval (view.symm locals))).run
      match returned with
      | .ok value =>
          let (control, scopedValues) ←
            observe (Env.equivProd.trans (Equiv.prodCongr (Equiv.refl _) view)) continuation
              program (value, locals)
          pure (control, scopedValues.2)
      | .error error => pure (.fault error, locals)) := by
  funext heap
  simp only [observe, action, eval_call, Prod.swap, ExceptT.run, Bind.bind, Pure.pure, StateT.bind,
    ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
  apply congrArg ((program.eval fn (args.eval (view.symm locals)) heap).bind)
  funext outcome
  rcases outcome with ⟨returned, finalHeap⟩
  cases returned with
  | ok value =>
      simp only [observe, action, Prod.swap, Bind.bind, StateT.bind,
        Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.prodCongr_apply,
        Equiv.prodCongr_symm,
        Env.equivProd_apply, Env.equivProd_symm_apply, State.cons, State.tail,
        ← Part.bind_some_eq_map, Part.bind_assoc, Part.bind_some]
      apply congrArg ((continuation.eval program
        ⟨Env.cons value (view.symm locals), finalHeap⟩).bind)
      funext outcome
      rcases outcome with ⟨⟨scopedLocals, bodyHeap⟩, control⟩
      rfl
  | error error =>
      simp only [Part.bind_some, Equiv.apply_symm_apply, StateT.pure]
      rfl

end Complexity.Language.Stmt
