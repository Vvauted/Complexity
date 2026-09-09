/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Control.Part
import Complexity.Language.Eval.Basic
import Complexity.Language.Verification
import Std.Do.Triple.Basic

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
-/

namespace Complexity.Language

open scoped Part.TotalCorrectness

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
