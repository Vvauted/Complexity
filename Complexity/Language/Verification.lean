/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Semantics

/-!
# Total correctness of typed source programs

`TotalWP` describes a finite execution of the independent source language.
Normal continuation and function return have separate postconditions; a fault
satisfies neither. The structural rules follow actual lexical values, callee
returns and branch conditions without mentioning a machine representation or
an instruction budget.
Local assignment evaluates the mathematical right-hand side in the entry state
and applies the normal postcondition to the updated state.
A while guard is itself a value-producing statement block. Its final state
feeds either the body or the exit. Well-founded descent covers a complete
guard-and-body iteration, without requiring descent on an early return.

`FunctionTotal` requires the declared body to return a value. Falling through
the body is not successful function termination. Function contracts compose
through the same `Exec.callReturn` rule as the source semantics.
Buffer rules bind the actual read value or slice and retain the actual heap
after a write. Their success conditions use the shared heap operations;
`Buffer.Contents` connects those operations to ordinary array specifications.
-/

namespace Complexity.Language

/-- Interpret two successful postconditions at a source control outcome.
Faults cannot establish total correctness. -/
def Control.Satisfies {Γ : List Ty} {result : Ty}
    (normal : State Γ → Prop) (returned : Value result → State Γ → Prop)
    (control : Control result) (finish : State Γ) : Prop :=
  match control with
  | .normal => normal finish
  | .returned value => returned value finish
  | .fault _ => False

/-- An escaping scope cannot establish either successful postcondition, even
when its body was already faulting. -/
@[simp] theorem Control.not_satisfies_scopeFailure {Γ : List Ty} {result : Ty}
    (control : Control result) (normal : State Γ → Prop)
    (returned : Value result → State Γ → Prop) (finish : State Γ) :
    ¬ control.scopeFailure.Satisfies normal returned finish := by
  cases control <;> simp [Control.scopeFailure, Control.Satisfies]

/-- The shared scope-exit operation establishes a successful postcondition
exactly when its roots are safe and the reclaimed current heap satisfies it. -/
@[simp] theorem scopeExit_satisfies_iff {Γ : List Ty} {result : Ty}
    (initial : Heap) (finish : State Γ) (control : Control result)
    (normal : State Γ → Prop) (returned : Value result → State Γ → Prop) :
    (scopeExit initial (finish, control)).2.Satisfies normal returned
      (scopeExit initial (finish, control)).1 ↔
      ScopeSafe initial finish control ∧
        control.Satisfies normal returned
          ⟨finish.locals, finish.heap.take initial.objects.size⟩ := by
  classical
  by_cases safe : ScopeSafe initial finish control
  · simp only [scopeExit_of_safe safe, safe, true_and]
  · simp only [scopeExit_of_not_safe safe, Control.not_satisfies_scopeFailure, safe, false_and]

/-- Budget-free total correctness, retaining both normal and returning control. -/
def TotalWP {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Program signatures) (stmt : Stmt signatures Γ result)
    (normal : State Γ → Prop) (returned : Value result → State Γ → Prop)
    (entry : State Γ) : Prop :=
  ∃ finish control, Exec program stmt entry finish control ∧
    control.Satisfies normal returned finish

namespace TotalWP

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Program signatures} {stmt : Stmt signatures Γ result}
variable {normal normal' : State Γ → Prop}
variable {returned returned' : Value result → State Γ → Prop} {entry : State Γ}

/-- Weaken either successful postcondition without admitting faults. -/
theorem mono_post (h : TotalWP program stmt normal returned entry)
    (hnormal : ∀ finish, normal finish → normal' finish)
    (hreturned : ∀ value finish, returned value finish → returned' value finish) :
    TotalWP program stmt normal' returned' entry := by
  obtain ⟨finish, control, execution, post⟩ := h
  refine ⟨finish, control, execution, ?_⟩
  cases control with
  | normal => exact hnormal finish post
  | returned value => exact hreturned value finish post
  | fault fault => exact post

@[simp] theorem skip_iff :
    TotalWP program .skip normal returned entry ↔ normal entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .normal, .skip entry, post⟩

/-- Assignment evaluates its right-hand side before updating the selected local.
The normal postcondition observes that update and the same current heap. -/
@[simp] theorem assign_iff {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ) :
    TotalWP program (.assign target value) normal returned entry ↔
      normal (entry.set target (value.eval entry.locals)) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry.set target (value.eval entry.locals), .normal,
      .assign target value entry, post⟩

@[simp] theorem ret_iff (value : Atom Γ result) :
    TotalWP program (.ret value) normal returned entry ↔
      returned (value.eval entry.locals) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution
    exact post
  · intro post
    exact ⟨entry, .returned (value.eval entry.locals), .ret value entry, post⟩

/-- A primitive's mathematical value is bound for its actual lexical scope. -/
@[simp] theorem letPrim_iff {τ : Ty} (value : Prim Γ τ)
    (continuation : Stmt signatures (τ :: Γ) result) :
    TotalWP program (.letPrim value continuation) normal returned entry ↔
      TotalWP program continuation (fun finish => normal finish.tail)
        (fun value finish => returned value finish.tail)
        (State.cons (value.eval entry.locals) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | letPrim body => exact ⟨_, control, body, post⟩
  · rintro ⟨finish, control, execution, post⟩
    exact ⟨finish.tail, control, .letPrim execution, post⟩

/-- Fresh allocation binds a completely initialized object in the extended
heap. Its continuation may mutate that heap or return the new handle; leaving
the lexical scope does not discard either effect. No machine capacity or time
budget belongs to this source-level correctness rule. -/
@[simp] theorem alloc_iff {kind : CellTy} (length : Atom Γ .nat)
    (initial : Atom Γ kind.toTy)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) :
    let allocated := entry.heap.alloc (length.eval entry.locals)
      (kind.ofValue (initial.eval entry.locals))
    TotalWP program (.alloc length initial continuation) normal returned entry ↔
      TotalWP program continuation (fun finish => normal finish.tail)
        (fun value finish => returned value finish.tail)
        (State.cons allocated.1 ⟨entry.locals, allocated.2⟩) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | alloc body => exact ⟨_, control, body, post⟩
  · rintro ⟨finish, control, execution, post⟩
    exact ⟨finish.tail, control, .alloc execution, post⟩

/-- A scope must finish successfully without retaining a reference to a fresh
object. Its postcondition observes the current contents of the entry objects,
after discarding only the newly allocated suffix. Returns pass through this
same exit check; an escaping exit is a fault and cannot establish total correctness. -/
@[simp] theorem scope_iff (body : Stmt signatures Γ result) :
    TotalWP program (.scope body) normal returned entry ↔
      TotalWP program body
        (fun finish => ScopeSafe entry.heap finish (.normal : Control result) ∧
          normal ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩)
        (fun value finish => ScopeSafe entry.heap finish (.returned value) ∧
          returned value ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩)
        entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | scope execution safe =>
        refine ⟨_, control, execution, ?_⟩
        cases control with
        | normal => exact ⟨safe, post⟩
        | returned value => exact ⟨safe, post⟩
        | fault error => exact False.elim post
    | scopeEscape execution escapes =>
        exact False.elim (Control.not_satisfies_scopeFailure _ _ _ _ post)
  · rintro ⟨finish, control, execution, post⟩
    cases control with
    | normal =>
        exact ⟨_, .normal, .scope execution post.1, post.2⟩
    | returned value =>
        exact ⟨_, .returned value, .scope execution post.1, post.2⟩
    | fault error => exact False.elim post

/-- A read must succeed and its actual current cell supplies the scoped value.
The continuation may change the heap, return early or execute further calls. -/
@[simp] theorem read_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (continuation : Stmt signatures (kind.toTy :: Γ) result) :
    TotalWP program (.read buffer index continuation) normal returned entry ↔
      ∃ value, entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value ∧
        TotalWP program continuation (fun finish => normal finish.tail)
          (fun result finish => returned result finish.tail)
          (State.cons (kind.toValue value) entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | read loaded body => exact ⟨_, loaded, _, control, body, post⟩
    | readFault failed => exact False.elim post
  · rintro ⟨value, loaded, finish, control, execution, post⟩
    exact ⟨finish.tail, control, .read loaded execution, post⟩

/-- A write must succeed and its actual new heap satisfies the normal
postcondition. It neither introduces a lexical binding nor returns a value. -/
@[simp] theorem write_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) :
    TotalWP program (.write buffer index value) normal returned entry ↔
      ∃ heap, entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap ∧ normal ⟨entry.locals, heap⟩ := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | write written => exact ⟨_, written, post⟩
    | writeFault failed => exact False.elim post
  · rintro ⟨heap, written, post⟩
    exact ⟨⟨entry.locals, heap⟩, .normal, .write written, post⟩

/-- A relative slice must fit the original view. The continuation receives the
actual new handle with the current heap, not a copy of the object's contents. -/
@[simp] theorem slice_iff {kind : CellTy} (buffer : Atom Γ (.buffer kind))
    (offset length : Atom Γ .nat)
    (continuation : Stmt signatures (.buffer kind :: Γ) result) :
    TotalWP program (.slice buffer offset length continuation) normal returned entry ↔
      ∃ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view ∧
        TotalWP program continuation (fun finish => normal finish.tail)
          (fun result finish => returned result finish.tail) (State.cons view entry) := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | slice sliced body => exact ⟨_, sliced, _, control, body, post⟩
    | sliceFault failed => exact False.elim post
  · rintro ⟨view, sliced, finish, control, execution, post⟩
    exact ⟨finish.tail, control, .slice sliced execution, post⟩

/-- Sequencing runs the tail only after normal continuation. An actual return
passes directly to the enclosing return postcondition. -/
@[simp] theorem seq_iff (first second : Stmt signatures Γ result) :
    TotalWP program (.seq first second) normal returned entry ↔
      TotalWP program first (TotalWP program second normal returned) returned entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | seqNormal firstExec secondExec =>
        exact ⟨_, .normal, firstExec, finish, control, secondExec, post⟩
    | seqReturn firstExec => exact ⟨_, _, firstExec, post⟩
    | seqFault firstExec => exact False.elim post
  · rintro ⟨middle, control, execution, post⟩
    cases control with
    | normal =>
        obtain ⟨finish, control, next, post⟩ := post
        exact ⟨finish, control, .seqNormal execution next, post⟩
    | returned value => exact ⟨middle, .returned value, .seqReturn execution, post⟩
    | fault fault => exact False.elim post

/-- Source branching depends on the actual Boolean value, not a machine guard. -/
@[simp] theorem ite_iff (condition : Atom Γ .bool) (yes no : Stmt signatures Γ result) :
    TotalWP program (.ite condition yes no) normal returned entry ↔
      if condition.eval entry.locals then TotalWP program yes normal returned entry
      else TotalWP program no normal returned entry := by
  cases hcondition : condition.eval entry.locals with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => cases hcondition.symm.trans truth
        | iteFalse truth body => exact ⟨finish, control, body, post⟩
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteFalse hcondition execution, post⟩
  | true =>
      simp only [↓reduceIte]
      constructor
      · rintro ⟨finish, control, execution, post⟩
        cases execution with
        | iteTrue truth body => exact ⟨finish, control, body, post⟩
        | iteFalse truth body => cases hcondition.symm.trans truth
      · rintro ⟨finish, control, execution, post⟩
        exact ⟨finish, control, .iteTrue hcondition execution, post⟩

/-- Unfold one iteration of an effectful guard loop. A guard must return a
Boolean; normal guard fallthrough and faults cannot establish total correctness.
Only a normally completing body repeats the loop at its actual final state.
This recursive equation is deliberately not a simplification rule. -/
theorem while_iff (guard : Stmt signatures Γ .bool) (body : Stmt signatures Γ result) :
    TotalWP program (.while guard body) normal returned entry ↔
      TotalWP program guard (fun _ => False)
        (fun test afterGuard =>
          if test then
            TotalWP program body (TotalWP program (.while guard body) normal returned)
              returned afterGuard
          else normal afterGuard) entry := by
  constructor
  · rintro ⟨finish, control, execution, post⟩
    cases execution with
    | whileFalse test => exact ⟨finish, .returned false, test, post⟩
    | whileTrue test iteration rest =>
        exact ⟨_, .returned true, test, _, .normal, iteration, finish, control, rest, post⟩
    | whileReturn test iteration =>
        exact ⟨_, .returned true, test, finish, _, iteration, post⟩
    | whileFault test iteration => exact False.elim post
    | whileGuardFault test => exact False.elim post
    | whileGuardMissingReturn test => exact False.elim post
  · rintro ⟨afterGuard, guardControl, test, post⟩
    cases guardControl with
    | normal => exact False.elim post
    | fault error => exact False.elim post
    | returned condition =>
        cases condition with
        | false => exact ⟨afterGuard, .normal, .whileFalse test, post⟩
        | true =>
            obtain ⟨afterBody, bodyControl, iteration, post⟩ := post
            cases bodyControl with
            | normal =>
                obtain ⟨finish, control, rest, post⟩ := post
                exact ⟨finish, control, .whileTrue test iteration rest, post⟩
            | returned value =>
                exact ⟨afterBody, .returned value, .whileReturn test iteration, post⟩
            | fault error => exact False.elim post

/-- An invariant before the guard and well-founded descent after a complete
normal iteration establish termination. The guard may update both locals and
heap. A false guard supplies the normal postcondition at its actual final state;
an early body return supplies the returning postcondition without further descent. -/
theorem while_wellFounded {guard : Stmt signatures Γ .bool}
    {body : Stmt signatures Γ result} {invariant : State Γ → Prop}
    {r : State Γ → State Γ → Prop} (wf : WellFounded r)
    (step : ∀ current, invariant current →
      TotalWP program guard (fun _ => False)
        (fun test afterGuard =>
          if test then
            TotalWP program body
              (fun afterBody => invariant afterBody ∧ r afterBody current)
              returned afterGuard
          else normal afterGuard) current)
    (initial : invariant entry) :
    TotalWP program (.while guard body) normal returned entry := by
  have loop : ∀ current, invariant current →
      TotalWP program (.while guard body) normal returned current := by
    intro current
    induction current using wf.induction with
    | h current ih =>
        intro preserved
        apply (while_iff guard body).mpr
        apply (step current preserved).mono_post (fun _ impossible => False.elim impossible)
        intro test afterGuard post
        cases test with
        | false => exact post
        | true =>
            exact post.mono_post
              (fun afterBody next => ih afterBody next.2 next.1) (fun _ _ h => h)
  exact loop entry initial

/-- A natural-number variant measures mathematical progress over a whole
guard-and-body iteration. It is independent of instruction costs or fuel. -/
theorem while_variant {guard : Stmt signatures Γ .bool}
    {body : Stmt signatures Γ result} {invariant : State Γ → Prop}
    (variant : State Γ → Nat)
    (step : ∀ current, invariant current →
      TotalWP program guard (fun _ => False)
        (fun test afterGuard =>
          if test then
            TotalWP program body
              (fun afterBody => invariant afterBody ∧ variant afterBody < variant current)
              returned afterGuard
          else normal afterGuard) current)
    (initial : invariant entry) :
    TotalWP program (.while guard body) normal returned entry :=
  while_wellFounded (measure variant).wf step initial

/-- Compose a primitive step after identifying its actual source value. -/
theorem letPrim {τ : Ty} {value : Prim Γ τ}
    {continuation : Stmt signatures (τ :: Γ) result}
    (body : TotalWP program continuation (fun finish => normal finish.tail)
      (fun value finish => returned value finish.tail)
      (State.cons (value.eval entry.locals) entry)) :
    TotalWP program (.letPrim value continuation) normal returned entry :=
  (letPrim_iff value continuation).mpr body

/-- Establish a local assignment using a mathematical postcondition on its
actual updated state; no additional lexical binding is introduced. -/
theorem assign {τ : Ty} {target : Var Γ τ} {value : Prim Γ τ}
    (post : normal (entry.set target (value.eval entry.locals))) :
    TotalWP program (.assign target value) normal returned entry :=
  (assign_iff target value).mpr post

/-- Close a source allocation scope after proving both the non-escape check
and the desired postcondition at the reclaimed current heap. -/
theorem scope
    (body : TotalWP program stmt
      (fun finish => ScopeSafe entry.heap finish (.normal : Control result) ∧
        normal ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩)
      (fun value finish => ScopeSafe entry.heap finish (.returned value) ∧
        returned value ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩) entry) :
    TotalWP program (.scope stmt) normal returned entry :=
  (scope_iff stmt).mpr body

/-- Reuse a body contract and discharge the two scope exits from its actual
normal and returning postconditions. No new termination argument is required. -/
theorem scope_compose (body : TotalWP program stmt normal' returned' entry)
    (normalExit : ∀ finish, normal' finish →
      ScopeSafe entry.heap finish (.normal : Control result) ∧
        normal ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩)
    (returnedExit : ∀ value finish, returned' value finish →
      ScopeSafe entry.heap finish (.returned value) ∧
        returned value ⟨finish.locals, finish.heap.take entry.heap.objects.size⟩) :
    TotalWP program (.scope stmt) normal returned entry :=
  scope (body.mono_post normalExit returnedExit)

/-- Compose a successful current-heap read with a proof about its actual value. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Stmt signatures (kind.toTy :: Γ) result} {value : CellValue kind}
    (loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value)
    (body : TotalWP program continuation (fun finish => normal finish.tail)
      (fun result finish => returned result finish.tail) (State.cons (kind.toValue value) entry)) :
    TotalWP program (.read buffer index continuation) normal returned entry :=
  (read_iff buffer index continuation).mpr ⟨value, loaded, body⟩

/-- Native array contents supply the mathematical value bound by a source read. -/
theorem read_contents {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat} {continuation : Stmt signatures (kind.toTy :: Γ) result}
    {contents : Array (CellValue kind)}
    (observed : (buffer.eval entry.locals).Contents entry.heap contents)
    (bound : index.eval entry.locals < contents.size)
    (body : TotalWP program continuation (fun finish => normal finish.tail)
      (fun result finish => returned result finish.tail)
      (State.cons (kind.toValue contents[index.eval entry.locals]) entry)) :
    TotalWP program (.read buffer index continuation) normal returned entry :=
  read (observed.read bound) body

/-- Compose the actual shared-heap update with a normal postcondition. -/
theorem write {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {value : Atom Γ kind.toTy} {heap : Heap}
    (written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
      (kind.ofValue (value.eval entry.locals)) = .ok heap)
    (post : normal ⟨entry.locals, heap⟩) :
    TotalWP program (.write buffer index value) normal returned entry :=
  (write_iff buffer index value).mpr ⟨heap, written, post⟩

/-- Compose a successful relative slice with its actual scoped borrowed view. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Stmt signatures (.buffer kind :: Γ) result} {view : Buffer kind}
    (sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view)
    (body : TotalWP program continuation (fun finish => normal finish.tail)
      (fun result finish => returned result finish.tail) (State.cons view entry)) :
    TotalWP program (.slice buffer offset length continuation) normal returned entry :=
  (slice_iff buffer offset length continuation).mpr ⟨view, sliced, body⟩

/-- Use a mathematical intermediate condition in a source sequence. -/
theorem seq {first second : Stmt signatures Γ result} {middle : State Γ → Prop}
    (head : TotalWP program first middle returned entry)
    (tail : ∀ next, middle next → TotalWP program second normal returned next) :
    TotalWP program (.seq first second) normal returned entry :=
  (seq_iff first second).mpr (head.mono_post tail (fun _ _ h => h))

end TotalWP

/-- A source function returns a value satisfying an ordinary mathematical
relation on its arguments and initial/final heaps. Neither a fault nor body
fallthrough is success. The initial heap is explicit, never defaulted to empty. -/
def FunctionTotal {signatures : List Signature} (program : Program signatures)
    (fn : Fin signatures.length) (pre : Env signatures[fn].params → Heap → Prop)
    (post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop) :
    Prop :=
  ∀ args heap, pre args heap → ∃ finish value,
    Exec program (program.body fn) ⟨args, heap⟩ finish (.returned value) ∧
      post args heap value finish.heap

namespace FunctionTotal

variable {signatures : List Signature} {program : Program signatures}
variable {fn : Fin signatures.length}
variable {pre pre' : Env signatures[fn].params → Heap → Prop}
variable {post post' : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}

/-- Source body verification supplies actual successful function termination. -/
theorem of_wp (body : ∀ args heap, pre args heap →
    TotalWP program (program.body fn) (fun _ => False)
      (fun value finish => post args heap value finish.heap) ⟨args, heap⟩) :
    FunctionTotal program fn pre post := by
  intro args heap hpre
  obtain ⟨finish, control, execution, hpost⟩ := body args heap hpre
  cases control with
  | normal => exact False.elim hpost
  | returned value => exact ⟨finish, value, execution, hpost⟩
  | fault fault => exact False.elim hpost

/-- A returned source execution is also a body WP proof. -/
theorem wp (h : FunctionTotal program fn pre post) (args : Env signatures[fn].params)
    (heap : Heap) (hpre : pre args heap) :
    TotalWP program (program.body fn) (fun _ => False)
      (fun value finish => post args heap value finish.heap) ⟨args, heap⟩ := by
  obtain ⟨finish, value, execution, hpost⟩ := h args heap hpre
  exact ⟨finish, .returned value, execution, hpost⟩

/-- Strengthen the source precondition and weaken the mathematical result relation. -/
theorem consequence (h : FunctionTotal program fn pre post)
    (hpre : ∀ args heap, pre' args heap → pre args heap)
    (hpost : ∀ args heap value finalHeap,
      pre' args heap → post args heap value finalHeap → post' args heap value finalHeap) :
    FunctionTotal program fn pre' post' := by
  intro args heap input
  obtain ⟨finish, value, execution, output⟩ := h args heap (hpre args heap input)
  exact ⟨finish, value, execution, hpost args heap value finish.heap input output⟩

/-- The mathematical postcondition describes any actual successful invocation,
not just the execution witness selected by a total-correctness proof. -/
theorem postcondition (h : FunctionTotal program fn pre post)
    {args : Env signatures[fn].params} {heap : Heap} {finish : State signatures[fn].params}
    {value : Value signatures[fn].result} (hpre : pre args heap)
    (execution : Exec program (program.body fn) ⟨args, heap⟩ finish (.returned value)) :
    post args heap value finish.heap := by
  obtain ⟨otherFinish, otherValue, otherExec, hpost⟩ := h args heap hpre
  obtain ⟨rfl, sameControl⟩ := otherExec.deterministic execution
  cases Control.returned.inj sameControl
  exact hpost

end FunctionTotal

namespace TotalWP

/-- Apply a source function's mathematical contract and bind its actual returned
value. Caller locals resume with the actual final callee heap; callee locals do
not escape their scope. The continuation reasons only about values and heaps. -/
theorem call {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {fn : Fin signatures.length}
    {args : Args Γ signatures[fn].params}
    {continuation : Stmt signatures (signatures[fn].result :: Γ) result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop} {entry : State Γ}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (callee : FunctionTotal program fn pre post)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value finalHeap, post (args.eval entry.locals) entry.heap value finalHeap →
      TotalWP program continuation (fun finish => normal finish.tail)
        (fun result finish => returned result finish.tail)
        (State.cons value ⟨entry.locals, finalHeap⟩)) :
    TotalWP program (.call fn args continuation) normal returned entry := by
  obtain ⟨calleeFinish, value, invocation, hpost⟩ :=
    callee (args.eval entry.locals) entry.heap hpre
  obtain ⟨finish, control, execution, result⟩ := body value calleeFinish.heap hpost
  exact ⟨finish.tail, control, .callReturn invocation execution, result⟩

end TotalWP

end Complexity.Language
