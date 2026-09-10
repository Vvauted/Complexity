/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Control.Part
import Complexity.Language.Eval.Basic
import Complexity.Language.Verification
import Std.Do.Triple.SpecLemmas

/-!
# Source correctness through the standard partial-value interfaces

The independent source verification rules agree with strict total correctness
for their `Part` observations. Functions can also be viewed through the existing
`ExceptT Fault (StateT Heap Part)` interface: a successful postcondition must be
reached at the actual final heap and the exceptional postcondition is false.
Divergence and finite faults therefore cannot prove these triples vacuously.

These adequacy theorems connect existing source proofs to ordinary result
equations and native `Std.Do.Triple`; they do not execute a lowered program or
replace its source implementation with a mathematical answer.

The native `Stmt.action` triple retains the complete final source state even
when control returns or faults. Its postcondition is the existing source
`Control.Satisfies`; hence faults and divergence cannot establish `TotalWP`.

The buffer actions have native `@[spec]` rules for `mvcgen`. Allocation exposes
its fresh identity, initialized contents and actual extended heap. Reads and slices
retain their actual current heap. Writes automatically establish success from
ordinary contents and an index bound; their continuation receives both the
updated contents and the real write equation, so existing alias and frame rules
remain available. These specifications introduce no second WP interpretation.
-/

namespace Complexity.Language

open scoped Part.TotalCorrectness

/-- A native successful triple is exactly termination with its ordinary result
and final-heap predicate. The false exceptional postcondition rejects faults. -/
theorem triple_iff_eval {α : Type} (action : ExceptT Fault (StateT Heap Part) α)
    (pre : Heap → Prop) (post : α → Heap → Prop) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) action (fun heap => ⟨pre heap⟩)
      (fun value heap => ⟨post value heap⟩, (fun _ _ => ⟨False⟩, ⟨⟩)) ↔
      ∀ heap, pre heap → ∃ value finish,
        action heap = Part.some (.ok value, finish) ∧ post value finish := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  constructor
  · intro specification heap input
    obtain ⟨⟨outcome, finish⟩, member, property⟩ := specification heap input
    cases outcome with
    | ok value => exact ⟨value, finish, Part.eq_some_iff.mpr member, property⟩
    | error _ => exact False.elim property
  · intro specification heap input
    obtain ⟨value, finish, returned, property⟩ := specification heap input
    exact ⟨(.ok value, finish), Part.eq_some_iff.mp returned, property⟩

namespace Buffer

/-- Allocation always terminates with its actual fresh handle and extended
heap. The continuation receives mathematical initialized contents, freshness
and shape growth together with the real allocation equation; no old heap is
restored and no finite-machine capacity or time budget is assumed. -/
@[spec] theorem allocM_spec {kind : CellTy} (length : Nat) (initial : CellValue kind)
    (post : Std.Do.PostCond (Buffer kind) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (allocM length initial)
      (fun heap => ⟨∀ buffer finish,
        heap.alloc length initial = (buffer, finish) →
        buffer.Contents finish (Array.replicate length initial) →
        heap.ShapeExtends finish → buffer.object = heap.objects.size →
        (post.1 buffer finish).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap property
  exact ⟨(.ok (heap.alloc length initial).1, (heap.alloc length initial).2),
    Part.eq_some_iff.mp (allocM_eq_ok length initial heap),
    property _ _ rfl (heap.alloc_contents length initial)
      (heap.shapeExtends_alloc length initial) (heap.alloc_object length initial)⟩

/-- A current-heap read binds the ordinary array element and preserves the
entire heap. Choosing mathematical contents is a ghost verification condition. -/
@[spec] theorem readM_spec {kind : CellTy} (buffer : Buffer kind) (index : Nat)
    (post : Std.Do.PostCond (CellValue kind) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (buffer.readM index)
      (fun heap => ⟨∃ contents : Array (CellValue kind), ∃ bound : index < contents.size,
        buffer.Contents heap contents ∧ (post.1 contents[index] heap).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap ⟨contents, bound, observed, property⟩
  exact ⟨(.ok contents[index], heap),
    Part.eq_some_iff.mp (readM_eq_ok (observed.read bound)), property⟩

/-- Ordinary contents and an index bound establish actual write termination.
The continuation receives its real effect equation as well as native updated
contents; no separation of overlapping borrowed views is imposed. -/
@[spec] theorem writeM_spec {kind : CellTy} (buffer : Buffer kind) (index : Nat)
    (value : CellValue kind)
    (post : Std.Do.PostCond Unit (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (buffer.writeM index value)
      (fun heap => ⟨∃ contents : Array (CellValue kind), ∃ bound : index < contents.size,
        buffer.Contents heap contents ∧ ∀ finish,
          heap.write buffer index value = .ok finish →
          buffer.Contents finish (contents.set index value bound) →
          (post.1 () finish).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap ⟨contents, bound, observed, property⟩
  obtain ⟨finish, written, updated⟩ := observed.write_exists bound value
  exact ⟨(.ok (), finish), Part.eq_some_iff.mp (writeM_eq_ok written),
    property finish written updated⟩

/-- A fitting relative slice returns the actual shared view and preserves the
entire heap. Its validity and contents can be derived using the existing view rules. -/
@[spec] theorem sliceM_spec {kind : CellTy} (buffer : Buffer kind) (offset length : Nat)
    (post : Std.Do.PostCond (Buffer kind) (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (buffer.sliceM offset length)
      (fun heap => ⟨offset + length ≤ buffer.length ∧
        (post.1 ⟨buffer.object, buffer.offset + offset, length⟩ heap).down⟩) post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro heap ⟨bound, property⟩
  exact ⟨(.ok ⟨buffer.object, buffer.offset + offset, length⟩, heap),
    Part.eq_some_iff.mp (sliceM_eq_ok (buffer.slice_eq bound) heap), property⟩

end Buffer

/-- Compose the standard state-action weakest precondition with the same scope
exit used by source execution. The body must produce an actual finite outcome;
the native postcondition then sees reclamation or the preserved escaping fault.
Successful source postconditions reduce this exit to its non-escape obligation. -/
@[spec] theorem Stmt.scope_action_spec {signatures : List Signature} {Γ : List Ty}
    {result : Ty} (program : Program signatures) (body : Stmt signatures Γ result)
    (post : Std.Do.PostCond (Control result) (.arg (State Γ) .pure)) :
    Std.Do.Triple (m := StateT (State Γ) Part) (ps := .arg (State Γ) .pure)
      ((Stmt.scope body).action program)
      (fun entry =>
        ((Std.Do.WP.wp (body.action program)).apply
          (fun control finish =>
            let exited := scopeExit entry.heap (finish, control)
            post.1 exited.2 exited.1, ⟨⟩)) entry)
      post := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  intro entry ⟨⟨control, finish⟩, execution, property⟩
  exact ⟨((scopeExit entry.heap (finish, control)).2,
      (scopeExit entry.heap (finish, control)).1),
    Stmt.mem_action_iff.mpr ((Stmt.mem_action_iff.mp execution).scope_exit), property⟩

/-- Source total correctness observes a real finite result and tests its
successful control postcondition. -/
theorem TotalWP.iff_eval {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop} {entry : State Γ} :
    TotalWP program stmt normal returned entry ↔
      ∃ outcome ∈ stmt.eval program entry, outcome.2.Satisfies normal returned outcome.1 := by
  constructor
  · rintro ⟨finish, control, execution, property⟩
    exact ⟨(finish, control), Stmt.mem_eval_iff.mpr execution, property⟩
  · rintro ⟨⟨finish, control⟩, member, property⟩
    exact ⟨finish, control, Stmt.mem_eval_iff.mp member, property⟩

/-- The scoped native weakest-precondition interface has exactly the existing
source total-correctness meaning, including rejection of faults. -/
theorem TotalWP.iff_wp_eval {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop} {entry : State Γ} :
    TotalWP program stmt normal returned entry ↔
      ((Std.Do.WP.wp (stmt.eval program entry)).apply
        (fun outcome => ⟨outcome.2.Satisfies normal returned outcome.1⟩, ⟨⟩)).down :=
  TotalWP.iff_eval

/-- Total correctness is the native triple of the same statement action from
the specified initial state. Normal and returned outcomes expose their actual
final locals and heap; the source postcondition rejects every fault. -/
theorem TotalWP.iff_triple_action {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Program signatures} {stmt : Stmt signatures Γ result}
    {normal : State Γ → Prop} {returned : Value result → State Γ → Prop} {entry : State Γ} :
    TotalWP program stmt normal returned entry ↔
      Std.Do.Triple (m := StateT (State Γ) Part) (ps := .arg (State Γ) .pure)
        (stmt.action program) (fun current => ⟨current = entry⟩)
        (fun control finish => ⟨control.Satisfies normal returned finish⟩, ⟨⟩) := by
  rw [TotalWP.iff_eval]
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushArg,
    Part.TotalCorrectness.wp]
  constructor
  · rintro ⟨⟨finish, control⟩, execution, post⟩ current rfl
    exact ⟨(control, finish), Stmt.mem_action_iff.mpr (Stmt.mem_eval_iff.mp execution), post⟩
  · intro specification
    obtain ⟨⟨control, finish⟩, execution, post⟩ := specification entry rfl
    exact ⟨(finish, control), Stmt.mem_eval_iff.mpr (Stmt.mem_action_iff.mp execution), post⟩

/-- A mathematical source contract gives an ordinary equation for its actual
partial function value, without reproving the implementation. -/
theorem FunctionTotal.eval_spec {signatures : List Signature} {program : Program signatures}
    {fn : Fin signatures.length} {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (specification : FunctionTotal program fn pre post)
    {args : Env signatures[fn].params} {initialHeap : Heap} (input : pre args initialHeap) :
    ∃ value finalHeap, program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
      post args initialHeap value finalHeap := by
  obtain ⟨finish, value, execution, property⟩ := specification args initialHeap input
  exact ⟨value, finish.heap, Program.eval_eq_ok_iff.mpr ⟨finish, execution, rfl⟩, property⟩

/-- Reuse a supplied source function contract in any native continuation
specification. The callee's actual returned value and final heap feed the
continuation, including when the callee changes shared objects. This theorem
does not unfold the callee or ask automation to choose a mathematical contract. -/
theorem FunctionTotal.triple_spec {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (specification : FunctionTotal program fn pre post) (args : Env signatures[fn].params)
    (continuation : Std.Do.PostCond (Value signatures[fn].result)
      (.except Fault (.arg Heap .pure))) :
    Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
      (ps := .except Fault (.arg Heap .pure)) (program.eval fn args)
      (fun initialHeap => ⟨pre args initialHeap ∧ ∀ value finalHeap,
        post args initialHeap value finalHeap → (continuation.1 value finalHeap).down⟩)
      continuation := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  intro initialHeap ⟨input, next⟩
  obtain ⟨value, finalHeap, returned, property⟩ :=
    specification.eval_spec (args := args) (initialHeap := initialHeap) input
  exact ⟨(.ok value, finalHeap), Part.eq_some_iff.mp returned, next value finalHeap property⟩

/-- Successful partial-value equations also establish the original total
source contract; this is an equivalence, not just a one-way proof view. -/
theorem FunctionTotal.iff_eval {signatures : List Signature} {program : Program signatures}
    {fn : Fin signatures.length} {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop} :
    FunctionTotal program fn pre post ↔
      ∀ args initialHeap, pre args initialHeap → ∃ value finalHeap,
        program.eval fn args initialHeap = Part.some (.ok value, finalHeap) ∧
          post args initialHeap value finalHeap := by
  constructor
  · intro specification args initialHeap input
    exact specification.eval_spec input
  · intro specification args initialHeap input
    obtain ⟨value, finalHeap, returned, property⟩ := specification args initialHeap input
    obtain ⟨finish, execution, sameHeap⟩ := Program.eval_eq_ok_iff.mp returned
    exact ⟨finish, value, execution, sameHeap.symm ▸ property⟩

/-- Transfer a mathematical specification of a pure function through its proved
source correspondence. The correspondence supplies successful termination and
preservation of every starting heap; the specification need not reason about
the source action or construct an execution witness. -/
theorem FunctionTotal.of_eval_eq_pure {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    (value : Env signatures[fn].params → Value signatures[fn].result)
    (correspondence : ∀ args, program.eval fn args = pure (value args))
    (specification : ∀ args heap, pre args heap → post args heap (value args) heap) :
    FunctionTotal program fn pre post := by
  apply FunctionTotal.iff_eval.mpr
  intro args heap input
  exact ⟨value args, heap, congrFun (correspondence args) heap, specification args heap input⟩

/-- Native exception/state triples express the same source function contract.
The initial heap is a ghost parameter, equated with the actual starting heap;
successful postconditions observe the final heap and faults have false postcondition. -/
theorem FunctionTotal.iff_triple_eval {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop} :
    FunctionTotal program fn pre post ↔ ∀ args initialHeap,
      Std.Do.Triple (m := ExceptT Fault (StateT Heap Part))
        (ps := .except Fault (.arg Heap .pure))
        (program.eval fn args)
        (fun currentHeap => ⟨currentHeap = initialHeap ∧ pre args initialHeap⟩)
        (fun value finalHeap => ⟨post args initialHeap value finalHeap⟩,
          (fun _ _ => ⟨False⟩, ⟨⟩)) := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Std.Do.PredTrans.pushArg, Part.TotalCorrectness.wp]
  constructor
  · rintro specification args initialHeap currentHeap ⟨rfl, input⟩
    obtain ⟨value, finalHeap, returned, property⟩ := specification.eval_spec input
    exact ⟨(.ok value, finalHeap), Part.eq_some_iff.mp returned, property⟩
  · intro specification
    apply FunctionTotal.iff_eval.mpr
    intro args initialHeap input
    obtain ⟨⟨outcome, finalHeap⟩, member, property⟩ :=
      specification args initialHeap initialHeap ⟨rfl, input⟩
    cases outcome with
    | ok value => exact ⟨value, finalHeap, Part.eq_some_iff.mpr member, property⟩
    | error _ => exact False.elim property

end Complexity.Language
