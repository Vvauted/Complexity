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
`ExceptT Fault Part` interface: a successful postcondition must be reached and
the exceptional postcondition is false. Divergence and finite faults therefore
cannot prove these triples vacuously.

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
    {normal : Env Γ → Prop} {returned : Value result → Env Γ → Prop} {entry : Env Γ} :
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
    {normal : Env Γ → Prop} {returned : Value result → Env Γ → Prop} {entry : Env Γ} :
    TotalWP program stmt normal returned entry ↔
      ((Std.Do.WP.wp (stmt.eval program entry)).apply
        (fun outcome => ⟨outcome.2.Satisfies normal returned outcome.1⟩, ⟨⟩)).down :=
  TotalWP.iff_eval

/-- A mathematical source contract gives an ordinary equation for its actual
partial function value, without reproving the implementation. -/
theorem FunctionTotal.eval_spec {signatures : List Signature} {program : Program signatures}
    {fn : Fin signatures.length} {pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop}
    (specification : FunctionTotal program fn pre post)
    {args : Env signatures[fn].params} (input : pre args) :
    ∃ value, program.eval fn args = Part.some (.ok value) ∧ post args value := by
  obtain ⟨finish, value, execution, property⟩ := specification args input
  exact ⟨value, Program.eval_eq_ok_iff.mpr ⟨finish, execution⟩, property⟩

/-- Successful partial-value equations also establish the original total
source contract; this is an equivalence, not just a one-way proof view. -/
theorem FunctionTotal.iff_eval {signatures : List Signature} {program : Program signatures}
    {fn : Fin signatures.length} {pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop} :
    FunctionTotal program fn pre post ↔
      ∀ args, pre args → ∃ value, program.eval fn args = Part.some (.ok value) ∧ post args value := by
  constructor
  · intro specification args input
    exact specification.eval_spec input
  · intro specification args input
    obtain ⟨value, returned, property⟩ := specification args input
    obtain ⟨finish, execution⟩ := Program.eval_eq_ok_iff.mp returned
    exact ⟨finish, value, execution, property⟩

/-- Native exception-aware Hoare triples express the same source function
contract. The standard `ExceptT` adapter is reused, with false fault postcondition. -/
theorem FunctionTotal.iff_triple_eval {signatures : List Signature}
    {program : Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Prop}
    {post : Env signatures[fn].params → Value signatures[fn].result → Prop} :
    FunctionTotal program fn pre post ↔ ∀ args,
      Std.Do.Triple (m := ExceptT Fault Part) (ps := .except Fault .pure)
        (program.eval fn args)
        ⟨pre args⟩ (fun value => ⟨post args value⟩, (fun _ => ⟨False⟩, ⟨⟩)) := by
  simp only [Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.pushExcept,
    Part.TotalCorrectness.wp, Std.Do.SPred.entails_nil]
  constructor
  · intro specification args input
    obtain ⟨value, returned, property⟩ := specification.eval_spec input
    exact ⟨.ok value, Part.eq_some_iff.mp returned, property⟩
  · intro specification
    apply FunctionTotal.iff_eval.mpr
    intro args input
    obtain ⟨outcome, member, property⟩ := specification args input
    cases outcome with
    | ok value => exact ⟨value, Part.eq_some_iff.mpr member, property⟩
    | error _ => exact False.elim property

end Complexity.Language
