/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.State
import Complexity.Language.Heap.Allocation
import Complexity.Language.Heap.Node
import Complexity.Language.Rooted
import Complexity.Language.Heap.Restriction

/-!
# Independent finite source execution

`Exec` relates a typed statement, its initial and final source states,
and its control outcome. It does not refer to a lowering, machine state, clock
or proposed time bound. Recursive calls execute the selected source body; the
inductive relation describes only finite executions, not assumed termination.

Returns and faults bypass later statements. Leaving a lexical binding removes
only that binding from the final environment. Calls evaluate their atomic
arguments in the caller, run a real body with independent callee locals and the
same shared heap, then bind the actual returned value in the caller's continuation.
Caller-local restoration retains the callee's actual final heap, including on
fault or missing return. A body that
falls through faults at this function boundary, including a Unit-returning body:
Unit must be returned explicitly and is not a default for a missing return.

Reads and writes operate on the current shared heap. A failed operation leaves
its entry state unchanged, without rolling back earlier effects. Slices check
their relative extent and bind another view of the same object, not a snapshot.
Node reads bind the stored head and identical optional tail from an actual
typed lookup. They do not traverse or validate the tail; an absent or wrongly
typed node faults without changing the heap.
Assignment evaluates its right-hand side in the current locals once, then updates
the selected local without changing the heap. Scope exit preserves assignments
to outer locals; caller restoration is lexical, not heap rollback.

Allocation appends a fresh initialized source object and binds its complete
view in the continuation. Returns and faults retain that continuation's actual
heap. Source allocation has no word capacity, out-of-memory result or cost.

An explicit allocation scope keeps the current contents of its entry objects
and discards only the fresh suffix, provided its final locals and any returned
value refer only to entry objects. Otherwise the complete final heap is retained
and the outcome faults with `regionEscape`, without overriding an earlier fault.
The scope does not catch a return or roll back local assignments and heap writes.

A loop evaluates its Boolean guard block anew before every iteration. The guard's
returned Boolean is local to that block; its actual final locals and heap feed
the body or the false exit. Body returns leave the enclosing loop immediately.
Guard fallthrough is a missing-return fault, not a false condition.

Option matching selects the actual constructor. Only a `some` branch binds a
payload, and leaving that branch drops only this binding while preserving its
outer-local updates, heap and control outcome.
-/

namespace Complexity.Language

/-- A finite source execution can fault instead of returning a value. -/
inductive Fault where
  | missingReturn
  | heap (error : Heap.Error)
  | regionEscape
  deriving DecidableEq, Repr

/-- Statement continuation, return from a value-producing block and failure are
distinct outcomes. A function catches its body return; a loop catches only its
Boolean guard's return, passing a body return to the enclosing computation. -/
inductive Control (result : Ty) where
  | normal
  | returned : Value result → Control result
  | fault : Fault → Control result

/-- Only a returned control outcome carries an object root of its own. -/
@[simp] def Control.Rooted {result : Ty} (control : Control result) (heap : Heap) : Prop :=
  match control with
  | .normal | .fault _ => True
  | .returned value => ValueRooted heap value

/-- A failed allocation-scope exit retains an earlier fault rather than masking it. -/
@[simp] def Control.scopeFailure {result : Ty} (control : Control result) : Control result :=
  match control with
  | .fault error => .fault error
  | .normal | .returned _ => .fault .regionEscape

/-- Every root retained on scope exit already belongs to the entry object domain.
Only object identities are checked, not buffer validity, contents or separation. -/
def ScopeSafe {Γ : List Ty} {result : Ty} (initial : Heap) (finish : State Γ)
    (control : Control result) : Prop :=
  finish.locals.Rooted initial ∧ control.Rooted initial

/-- Apply the allocation-scope boundary to an already determined body outcome.
Safe exits discard only fresh objects from the actual final heap. Unsafe exits
retain that heap and report failure without masking an existing fault. This is
an outcome conversion, not an evaluator for source statements. -/
noncomputable def scopeExit {Γ : List Ty} {result : Ty} (initial : Heap)
    (outcome : State Γ × Control result) : State Γ × Control result := by
  classical
  exact if ScopeSafe initial outcome.1 outcome.2 then
    (⟨outcome.1.locals, outcome.1.heap.take initial.objects.size⟩, outcome.2)
  else (outcome.1, outcome.2.scopeFailure)

/-- A safe boundary preserves control and the current contents of retained objects. -/
@[simp] theorem scopeExit_of_safe {Γ : List Ty} {result : Ty} {initial : Heap}
    {finish : State Γ} {control : Control result} (safe : ScopeSafe initial finish control) :
    scopeExit initial (finish, control) =
      (⟨finish.locals, finish.heap.take initial.objects.size⟩, control) := by
  simp only [scopeExit, if_pos safe]

/-- An unsafe boundary does not leave handles dangling by discarding their objects. -/
@[simp] theorem scopeExit_of_not_safe {Γ : List Ty} {result : Ty} {initial : Heap}
    {finish : State Γ} {control : Control result} (escapes : ¬ ScopeSafe initial finish control) :
    scopeExit initial (finish, control) = (finish, control.scopeFailure) := by
  simp only [scopeExit, if_neg escapes]

/-- Finite execution of the source syntax itself. The state of each
statement is separate from its control outcome; scoped and call bindings are
removed on exit without swallowing returns or faults. -/
inductive Exec {signatures : List Signature} (program : Program signatures) :
    {Γ : List Ty} → {result : Ty} → Stmt signatures Γ result →
      State Γ → State Γ → Control result → Prop where
  | skip {Γ : List Ty} {result : Ty} (entry : State Γ) :
      Exec program (.skip : Stmt signatures Γ result) entry entry .normal
  | assign {Γ : List Ty} {τ result : Ty} (target : Var Γ τ) (value : Prim Γ τ)
      (entry : State Γ) :
      Exec program (.assign target value : Stmt signatures Γ result) entry
        (entry.set target (value.eval entry.locals)) .normal
  | letPrim {Γ : List Ty} {τ result : Ty} {value : Prim Γ τ}
      {continuation : Stmt signatures (τ :: Γ) result}
      {entry : State Γ} {finish : State (τ :: Γ)} {control : Control result}
      (body : Exec program continuation (State.cons (value.eval entry.locals) entry)
        finish control) :
      Exec program (.letPrim value continuation) entry finish.tail control
  | read {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Stmt signatures (kind.toTy :: Γ) result}
      {entry : State Γ} {finish : State (kind.toTy :: Γ)} {control : Control result}
      {value : CellValue kind}
      (loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value)
      (body : Exec program continuation (State.cons (kind.toValue value) entry) finish control) :
      Exec program (.read buffer index continuation) entry finish.tail control
  | readFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Stmt signatures (kind.toTy :: Γ) result}
      {entry : State Γ} {error : Heap.Error}
      (failed : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .error error) :
      Exec program (.read buffer index continuation) entry entry (.fault (.heap error))
  | readNode {Γ : List Ty} {result : Ty} {kind : CellTy}
      {ref : Atom Γ (.node kind)}
      {continuation : Stmt signatures (.prod kind.toTy (.option (.node kind)) :: Γ) result}
      {entry : State Γ}
      {finish : State (.prod kind.toTy (.option (.node kind)) :: Γ)}
      {control : Control result} {head : CellValue kind} {tail : Option (NodeRef kind)}
      (loaded : entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail))
      (body : Exec program continuation (State.cons (kind.toValue head, tail) entry)
        finish control) :
      Exec program (.readNode ref continuation) entry finish.tail control
  | readNodeFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {ref : Atom Γ (.node kind)}
      {continuation : Stmt signatures (.prod kind.toTy (.option (.node kind)) :: Γ) result}
      {entry : State Γ}
      (missing : entry.heap.node? kind (ref.eval entry.locals).object = none) :
      Exec program (.readNode ref continuation) entry entry (.fault (.heap .invalidObject))
  | consNode {Γ : List Ty} {result : Ty} {kind : CellTy}
      {head : Atom Γ kind.toTy} {tail : Atom Γ (.option (.node kind))}
      {continuation : Stmt signatures (.node kind :: Γ) result}
      {entry : State Γ} {finish : State (.node kind :: Γ)} {control : Control result}
      (body : Exec program continuation
        (let allocated := entry.heap.cons (kind.ofValue (head.eval entry.locals))
          (tail.eval entry.locals)
         State.cons allocated.1 ⟨entry.locals, allocated.2⟩)
        finish control) :
      Exec program (.consNode head tail continuation) entry finish.tail control
  | write {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : State Γ} {heap : Heap}
      (written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap) :
      Exec program (.write buffer index value : Stmt signatures Γ result)
        entry ⟨entry.locals, heap⟩ .normal
  | writeFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : State Γ} {error : Heap.Error}
      (failed : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .error error) :
      Exec program (.write buffer index value : Stmt signatures Γ result)
        entry entry (.fault (.heap error))
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Stmt signatures (.buffer kind :: Γ) result}
      {entry : State Γ} {finish : State (.buffer kind :: Γ)} {control : Control result}
      {view : Buffer kind}
      (sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view)
      (body : Exec program continuation (State.cons view entry) finish control) :
      Exec program (.slice buffer offset length continuation) entry finish.tail control
  | sliceFault {Γ : List Ty} {result : Ty} {kind : CellTy}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Stmt signatures (.buffer kind :: Γ) result}
      {entry : State Γ} {error : Heap.Error}
      (failed : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .error error) :
      Exec program (.slice buffer offset length continuation) entry entry (.fault (.heap error))
  | alloc {Γ : List Ty} {result : Ty} {kind : CellTy}
      {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
      {continuation : Stmt signatures (.buffer kind :: Γ) result}
      {entry : State Γ} {finish : State (.buffer kind :: Γ)} {control : Control result}
      (body : Exec program continuation
        (let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
          (kind.ofValue (initial.eval entry.locals))
         State.cons allocated.1 ⟨entry.locals, allocated.2⟩)
        finish control) :
      Exec program (.alloc length initial continuation) entry finish.tail control
  | scope {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
      {entry finish : State Γ} {control : Control result}
      (body : Exec program stmt entry finish control)
      (safe : ScopeSafe entry.heap finish control) :
      Exec program (.scope stmt) entry
        ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩ control
  | scopeEscape {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
      {entry finish : State Γ} {control : Control result}
      (body : Exec program stmt entry finish control)
      (escapes : ¬ ScopeSafe entry.heap finish control) :
      Exec program (.scope stmt) entry finish control.scopeFailure
  | seqNormal {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry middle finish : State Γ} {control : Control result}
      (head : Exec program first entry middle .normal)
      (tail : Exec program second middle finish control) :
      Exec program (.seq first second) entry finish control
  | seqReturn {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : State Γ} {value : Value result}
      (head : Exec program first entry finish (.returned value)) :
      Exec program (.seq first second) entry finish (.returned value)
  | seqFault {Γ : List Ty} {result : Ty} {first second : Stmt signatures Γ result}
      {entry finish : State Γ} {error : Fault}
      (head : Exec program first entry finish (.fault error)) :
      Exec program (.seq first second) entry finish (.fault error)
  | iteTrue {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : State Γ} {control : Control result}
      (test : condition.eval entry.locals = true)
      (body : Exec program yes entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | iteFalse {Γ : List Ty} {result : Ty} {condition : Atom Γ .bool}
      {yes no : Stmt signatures Γ result} {entry finish : State Γ} {control : Control result}
      (test : condition.eval entry.locals = false)
      (body : Exec program no entry finish control) :
      Exec program (.ite condition yes no) entry finish control
  | matchNone {Γ : List Ty} {result τ : Ty} {value : Atom Γ (.option τ)}
      {noneBranch : Stmt signatures Γ result}
      {someBranch : Stmt signatures (τ :: Γ) result}
      {entry finish : State Γ} {control : Control result}
      (selected : value.eval entry.locals = none)
      (body : Exec program noneBranch entry finish control) :
      Exec program (.matchOption value noneBranch someBranch) entry finish control
  | matchSome {Γ : List Ty} {result τ : Ty} {value : Atom Γ (.option τ)}
      {noneBranch : Stmt signatures Γ result}
      {someBranch : Stmt signatures (τ :: Γ) result}
      {entry : State Γ} {payload : Value τ} {finish : State (τ :: Γ)}
      {control : Control result}
      (selected : value.eval entry.locals = some payload)
      (body : Exec program someBranch (State.cons payload entry) finish control) :
      Exec program (.matchOption value noneBranch someBranch) entry finish.tail control
  | whileFalse {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry finish : State Γ}
      (test : Exec program guard entry finish (.returned false)) :
      Exec program (.while guard body) entry finish .normal
  | whileTrue {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry afterGuard afterBody finish : State Γ}
      {control : Control result}
      (test : Exec program guard entry afterGuard (.returned true))
      (iteration : Exec program body afterGuard afterBody .normal)
      (rest : Exec program (.while guard body) afterBody finish control) :
      Exec program (.while guard body) entry finish control
  | whileReturn {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry afterGuard finish : State Γ}
      {value : Value result}
      (test : Exec program guard entry afterGuard (.returned true))
      (iteration : Exec program body afterGuard finish (.returned value)) :
      Exec program (.while guard body) entry finish (.returned value)
  | whileFault {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry afterGuard finish : State Γ} {error : Fault}
      (test : Exec program guard entry afterGuard (.returned true))
      (iteration : Exec program body afterGuard finish (.fault error)) :
      Exec program (.while guard body) entry finish (.fault error)
  | whileGuardFault {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry finish : State Γ} {error : Fault}
      (test : Exec program guard entry finish (.fault error)) :
      Exec program (.while guard body) entry finish (.fault error)
  | whileGuardMissingReturn {Γ : List Ty} {result : Ty} {guard : Stmt signatures Γ .bool}
      {body : Stmt signatures Γ result} {entry finish : State Γ}
      (test : Exec program guard entry finish .normal) :
      Exec program (.while guard body) entry finish (.fault .missingReturn)
  | ret {Γ : List Ty} {result : Ty} (value : Atom Γ result) (entry : State Γ) :
      Exec program (.ret value) entry entry (.returned (value.eval entry.locals))
  | callReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params}
      {value : Value signatures[fn].result} {finish : State (signatures[fn].result :: Γ)}
      {control : Control result}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish (.returned value))
      (body : Exec program continuation (State.cons value (entry.restore calleeFinish))
        finish control) :
      Exec program (.call fn args continuation) entry finish.tail control
  | callFault {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params} {error : Fault}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish (.fault error)) :
      Exec program (.call fn args continuation) entry (entry.restore calleeFinish) (.fault error)
  | callMissingReturn {Γ : List Ty} {result : Ty} {fn : Fin signatures.length}
      {args : Args Γ signatures[fn].params}
      {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : State Γ} {calleeFinish : State signatures[fn].params}
      (callee : Exec program (program.body fn) (entry.enter (args.eval entry.locals))
        calleeFinish .normal) :
      Exec program (.call fn args continuation) entry (entry.restore calleeFinish)
        (.fault .missingReturn)

namespace Exec

/-- The outcome conversion is justified by the two actual scope execution rules. -/
theorem scope_exit {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (body : Exec program stmt entry finish control) :
    Exec program (.scope stmt) entry (scopeExit entry.heap (finish, control)).1
      (scopeExit entry.heap (finish, control)).2 := by
  classical
  by_cases safe : ScopeSafe entry.heap finish control
  · simpa only [scopeExit_of_safe safe] using Exec.scope body safe
  · simpa only [scopeExit_of_not_safe safe] using Exec.scopeEscape body safe

/-- Statements with no local writes preserve their enclosing environment even
when the shared heap changes. Callee-local assignment is allowed: calls restore
the caller's locals before executing its continuation. -/
theorem locals_eq {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish : State Γ} {control : Control result}
    (execution : Exec program stmt entry finish control) (unchanged : stmt.NoLocalWrites) :
    finish.locals = entry.locals := by
  revert unchanged
  induction execution with
  | skip => intro _; rfl
  | assign => intro impossible; exact False.elim impossible
  | letPrim body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | read loaded body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | readFault => intro _; rfl
  | readNode loaded body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | readNodeFault => intro _; rfl
  | consNode body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | write => intro _; rfl
  | writeFault => intro _; rfl
  | slice sliced body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | sliceFault => intro _; rfl
  | alloc body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged)
  | scope body safe ih => intro unchanged; exact ih unchanged
  | scopeEscape body escapes ih => intro unchanged; exact ih unchanged
  | seqNormal head tail ihHead ihTail =>
      intro unchanged
      exact (ihTail unchanged.2).trans (ihHead unchanged.1)
  | seqReturn head ih => intro unchanged; exact ih unchanged.1
  | seqFault head ih => intro unchanged; exact ih unchanged.1
  | iteTrue test body ih => intro unchanged; exact ih unchanged.1
  | iteFalse test body ih => intro unchanged; exact ih unchanged.2
  | matchNone selected body ih => intro unchanged; exact ih unchanged.1
  | matchSome selected body ih =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons] using
        congrArg Env.tail (ih unchanged.2)
  | whileFalse test ih => intro unchanged; exact ih unchanged.1
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      intro unchanged
      exact (ihRest unchanged).trans ((ihIteration unchanged.2).trans (ihTest unchanged.1))
  | whileReturn test iteration ihTest ihIteration =>
      intro unchanged
      exact (ihIteration unchanged.2).trans (ihTest unchanged.1)
  | whileFault test iteration ihTest ihIteration =>
      intro unchanged
      exact (ihIteration unchanged.2).trans (ihTest unchanged.1)
  | whileGuardFault test ih => intro unchanged; exact ih unchanged.1
  | whileGuardMissingReturn test ih => intro unchanged; exact ih unchanged.1
  | ret => intro _; rfl
  | callReturn callee body ihCallee ihBody =>
      intro unchanged
      simpa only [State.locals_tail, State.locals_cons, Env.tail_cons, State.locals_restore] using
        congrArg Env.tail (ihBody unchanged)
  | callFault => intro _; rfl
  | callMissingReturn => intro _; rfl

/-- The same source statement and entry state determine both its final state
and its finite control outcome, independently of execution proofs. -/
theorem deterministic {signatures : List Signature} {program : Program signatures}
    {Γ : List Ty} {result : Ty} {stmt : Stmt signatures Γ result}
    {entry finish finish' : State Γ} {control control' : Control result}
    (first : Exec program stmt entry finish control)
    (second : Exec program stmt entry finish' control') :
    finish = finish' ∧ control = control' := by
  induction first with
  | skip =>
      cases second
      exact ⟨rfl, rfl⟩
  | assign =>
      cases second
      exact ⟨rfl, rfl⟩
  | letPrim body ih =>
      cases second with
      | letPrim body' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | read loaded body ih =>
      cases second with
      | read loaded' body' =>
          cases Except.ok.inj (loaded.symm.trans loaded')
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | readFault failed => cases loaded.symm.trans failed
  | readFault failed =>
      cases second with
      | read loaded body => cases failed.symm.trans loaded
      | readFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | readNode loaded body ih =>
      cases second with
      | readNode loaded' body' =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (loaded.symm.trans loaded'))
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | readNodeFault missing => cases loaded.symm.trans missing
  | readNodeFault missing =>
      cases second with
      | readNode loaded body => cases missing.symm.trans loaded
      | readNodeFault => exact ⟨rfl, rfl⟩
  | write written =>
      cases second with
      | write written' =>
          cases Except.ok.inj (written.symm.trans written')
          exact ⟨rfl, rfl⟩
      | writeFault failed => cases written.symm.trans failed
  | writeFault failed =>
      cases second with
      | write written => cases failed.symm.trans written
      | writeFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | slice sliced body ih =>
      cases second with
      | slice sliced' body' =>
          cases Except.ok.inj (sliced.symm.trans sliced')
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | sliceFault failed => cases sliced.symm.trans failed
  | sliceFault failed =>
      cases second with
      | slice sliced body => cases failed.symm.trans sliced
      | sliceFault failed' =>
          cases Except.error.inj (failed.symm.trans failed')
          exact ⟨rfl, rfl⟩
  | alloc body ih =>
      cases second with
      | alloc body' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | consNode body ih =>
      cases second with
      | consNode body' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | scope body safe ih =>
      cases second with
      | scope body' safe' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
      | scopeEscape body' escapes =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact False.elim (escapes safe)
  | scopeEscape body escapes ih =>
      cases second with
      | scope body' safe =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact False.elim (escapes safe)
      | scopeEscape body' escapes' =>
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | seqNormal head tail ihHead ihTail =>
      cases second with
      | seqNormal head' tail' =>
          obtain ⟨rfl, _⟩ := ihHead head'
          exact ihTail tail'
      | seqReturn head' => cases (ihHead head').2
      | seqFault head' => cases (ihHead head').2
  | seqReturn head ih =>
      cases second with
      | seqNormal head' tail' => cases (ih head').2
      | seqReturn head' => exact ih head'
      | seqFault head' => cases (ih head').2
  | seqFault head ih =>
      cases second with
      | seqNormal head' tail' => cases (ih head').2
      | seqReturn head' => cases (ih head').2
      | seqFault head' => exact ih head'
  | iteTrue test body ih =>
      cases second with
      | iteTrue test' body' => exact ih body'
      | iteFalse test' body' => simp_all
  | iteFalse test body ih =>
      cases second with
      | iteTrue test' body' => simp_all
      | iteFalse test' body' => exact ih body'
  | matchNone selected body ih =>
      cases second with
      | matchNone selected' body' => exact ih body'
      | matchSome selected' body' => cases selected.symm.trans selected'
  | matchSome selected body ih =>
      cases second with
      | matchNone selected' body' => cases selected.symm.trans selected'
      | matchSome selected' body' =>
          cases Option.some.inj (selected.symm.trans selected')
          obtain ⟨rfl, rfl⟩ := ih body'
          exact ⟨rfl, rfl⟩
  | whileFalse test ih =>
      cases second with
      | whileFalse test' =>
          obtain ⟨rfl, _⟩ := ih test'
          exact ⟨rfl, rfl⟩
      | whileTrue test' iteration' rest' => cases (ih test').2
      | whileReturn test' iteration' => cases (ih test').2
      | whileFault test' iteration' => cases (ih test').2
      | whileGuardFault test' => cases (ih test').2
      | whileGuardMissingReturn test' => cases (ih test').2
  | whileTrue test iteration rest ihTest ihIteration ihRest =>
      cases second with
      | whileFalse test' => cases (ihTest test').2
      | whileTrue test' iteration' rest' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          obtain ⟨rfl, _⟩ := ihIteration iteration'
          exact ihRest rest'
      | whileReturn test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileFault test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileGuardFault test' => cases (ihTest test').2
      | whileGuardMissingReturn test' => cases (ihTest test').2
  | whileReturn test iteration ihTest ihIteration =>
      cases second with
      | whileFalse test' => cases (ihTest test').2
      | whileTrue test' iteration' rest' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileReturn test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          exact ihIteration iteration'
      | whileFault test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileGuardFault test' => cases (ihTest test').2
      | whileGuardMissingReturn test' => cases (ihTest test').2
  | whileFault test iteration ihTest ihIteration =>
      cases second with
      | whileFalse test' => cases (ihTest test').2
      | whileTrue test' iteration' rest' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileReturn test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          cases (ihIteration iteration').2
      | whileFault test' iteration' =>
          obtain ⟨rfl, _⟩ := ihTest test'
          exact ihIteration iteration'
      | whileGuardFault test' => cases (ihTest test').2
      | whileGuardMissingReturn test' => cases (ihTest test').2
  | whileGuardFault test ih =>
      cases second with
      | whileFalse test' => cases (ih test').2
      | whileTrue test' iteration' rest' => cases (ih test').2
      | whileReturn test' iteration' => cases (ih test').2
      | whileFault test' iteration' => cases (ih test').2
      | whileGuardFault test' =>
          obtain ⟨rfl, sameControl⟩ := ih test'
          cases Control.fault.inj sameControl
          exact ⟨rfl, rfl⟩
      | whileGuardMissingReturn test' => cases (ih test').2
  | whileGuardMissingReturn test ih =>
      cases second with
      | whileFalse test' => cases (ih test').2
      | whileTrue test' iteration' rest' => cases (ih test').2
      | whileReturn test' iteration' => cases (ih test').2
      | whileFault test' iteration' => cases (ih test').2
      | whileGuardFault test' => cases (ih test').2
      | whileGuardMissingReturn test' =>
          obtain ⟨rfl, _⟩ := ih test'
          exact ⟨rfl, rfl⟩
  | ret =>
      cases second
      exact ⟨rfl, rfl⟩
  | callReturn callee body ihCallee ihBody =>
      cases second with
      | callReturn callee' body' =>
          obtain ⟨rfl, sameControl⟩ := ihCallee callee'
          cases Control.returned.inj sameControl
          obtain ⟨rfl, rfl⟩ := ihBody body'
          exact ⟨rfl, rfl⟩
      | callFault callee' => cases (ihCallee callee').2
      | callMissingReturn callee' => cases (ihCallee callee').2
  | callFault callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' =>
          obtain ⟨rfl, sameControl⟩ := ih callee'
          cases Control.fault.inj sameControl
          exact ⟨rfl, rfl⟩
      | callMissingReturn callee' => cases (ih callee').2
  | callMissingReturn callee ih =>
      cases second with
      | callReturn callee' body' => cases (ih callee').2
      | callFault callee' => cases (ih callee').2
      | callMissingReturn callee' =>
          obtain ⟨rfl, _⟩ := ih callee'
          exact ⟨rfl, rfl⟩

end Exec

end Complexity.Language
