/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Array.MergeSort.Total
import Ram.Verification.Specification
import Ram.Verification.StateMCall
import Std.Tactic.Do

/-!
# A native stateful specification of the existing RAM merge sort

`sortState` is the ordinary mathematical specification `modify sorted`.
The existing recursive RAM function implements it; no host-side sorting
operation is added to the RAM program. Its callable refinement preserves the
source array, scratch extent, memory outside both buffers and I/O, and the
generic native-call bridge restores the caller's other registers.

The fixed extent and original entry are ghost parameters of the representation,
not specializations of the statement or function table. The native triple
supplies a reusable functional postcondition, while running time remains a
separate proof about the same implementation.
-/

namespace Ram.Source.Array.MergeSort

/-- Native state effects describe the ordinary canonical sorted result. -/
def sortState : StateM (List (Word w)) PUnit := modify sorted

open Std.Do in
/-- A native Hoare proof concerns lists, not RAM registers or fuel. -/
theorem sortState_spec (xs : List (Word w)) :
    ⦃fun state => ⌜state = xs⌝⦄ sortState
    ⦃⇓ _ state => ⌜state = sorted xs⌝⦄ := by
  mvcgen [sortState]
  exact congrArg sorted ‹_ = xs›

/-- Array heap assertions and endpoint frames depend only on shared memory
and I/O. The two array clauses are exactly `ArrayAt` with registers omitted. -/
def SharedStateRep (heapLimit : Nat) (base scratch : Word w) (length : Nat)
    (original : State w) (values : List (Word w)) (mem : Word w → Word w)
    (input outputRev : List (Word w)) : Prop :=
  (ArrayRep mem base values ∧ base.toNat + values.length ≤ heapLimit) ∧
  (∃ workspace, workspace.length = length ∧
    (ArrayRep mem scratch workspace ∧ scratch.toNat + workspace.length ≤ heapLimit)) ∧
  TwoBufferFrame base length scratch length original.mem mem ∧
  input = original.input ∧ outputRev = original.outputRev

/-- Calling the existing three-parameter function binds the supplied pointers
and length while retaining both shared array assertions. -/
theorem Pre.enter_params {heapLimit : Nat} {base scratch : Word w}
    {xs : List (Word w)} {entry : State w} (h : Pre heapLimit base scratch xs entry) :
    Pre heapLimit base scratch xs
      (entry.enter ([Expr.var 0, .var 1, .var 2].map entry.eval)) := by
  refine ⟨h.source_array.enter _, ?_, h.disjoint, ?_, ?_, ?_⟩
  · obtain ⟨workspace, length, represented⟩ := h.scratch_array
    exact ⟨workspace, length, represented.enter _⟩
  · simpa [State.enter, State.eval, Expr.eval] using h.base_reg
  · simpa [State.enter, State.eval, Expr.eval] using h.scratch_reg
  · simpa [State.enter, State.eval, Expr.eval] using h.length_reg

variable {w heapLimit selfFn : Nat} {functions : Program}

/-- The separately proved functional recursion implements the native model,
including scratch storage and the frame relative to the original caller. -/
theorem body_stateM_refines {base scratch : Word w} (length : Nat) (original : State w)
    (hw : 2 ≤ w) (lookup : functions[selfFn]? = some (function selfFn)) :
    Refines functions heapLimit (Nat.clog 2 length) (function selfFn).body
      (fun xs entry => xs.length = length ∧ Pre heapLimit base scratch xs entry ∧
        entry.mem = original.mem ∧ entry.input = original.input ∧
        entry.outputRev = original.outputRev)
      (fun result finish =>
        (function selfFn).result.ReadsBelow heapLimit finish.regs finish.mem ∧
        finish.eval (function selfFn).result = 0 ∧
        SharedStateRep heapLimit base scratch length original result.2
          finish.mem finish.input finish.outputRev)
      (sortState (w := w)).run := by
  rintro xs entry ⟨hlen, hp, hmem, hin, hout⟩
  have specPre : (recursionSpec heapLimit selfFn w).toTotal.pre xs entry := by
    change Pre heapLimit (entry.regs 0) (entry.regs 1) xs entry
    simpa only [hp.base_reg, hp.scratch_reg] using hp
  have correct := recursive_total (heapLimit := heapLimit) hw lookup xs
  change TotalRelContract functions heapLimit (Nat.clog 2 xs.length) (function selfFn).body
    ((recursionSpec heapLimit selfFn w).pre xs)
    (fun start finish => (function selfFn).result.ReadsBelow heapLimit finish.regs finish.mem ∧
      (recursionSpec heapLimit selfFn w).post xs start finish) at correct
  apply Verification.TotalWP.of_relContract
    (correct.mono_depth (depth' := Nat.clog 2 length)
      (Nat.le_of_eq (congrArg (Nat.clog 2) hlen))) specPre
  rintro finish ⟨reads, result⟩
  have post : Post heapLimit base scratch xs entry finish := by
    change Post heapLimit (entry.regs 0) (entry.regs 1) xs entry finish at result
    simpa only [hp.base_reg, hp.scratch_reg] using result
  refine ⟨reads, rfl, post.source_array, ?_, ?_,
    post.input.trans hin, post.output.trans hout⟩
  · obtain ⟨workspace, hworkspace, represented⟩ := post.scratch_array
    exact ⟨workspace, hworkspace.trans hlen, represented⟩
  · simpa only [hlen, hmem] using post.frame

/-- The generic native-call bridge supplies return decoding and local-frame
restoration; this theorem only supplies the existing sort's argument binding. -/
theorem call_stateM_refines {base scratch : Word w} (length : Nat) (original : State w)
    (dst : Reg) (hw : 2 ≤ w)
    (lookup : functions[selfFn]? = some (function selfFn)) :
    Refines functions heapLimit (Nat.clog 2 length + 1)
      (.call dst selfFn [.var 0, .var 1, .var 2])
      (fun xs entry => xs.length = length ∧ Pre heapLimit base scratch xs entry ∧
        entry = original)
      (fun result finish => finish.regs dst = 0 ∧
        SharedStateRep heapLimit base scratch length original result.2
          finish.mem finish.input finish.outputRev ∧
        ∀ r, r ≠ dst → finish.regs r = original.regs r)
      (sortState (w := w)).run := by
  have called := (body_stateM_refines (heapLimit := heapLimit) (base := base) (scratch := scratch)
    length original hw lookup).stateM_call (dst := dst) (args := [.var 0, .var 1, .var 2])
      (returnRep := fun (_ : PUnit) value => value = 0) original lookup rfl
      (by change 3 ≤ 9; decide)
      (by simp [Expr.ReadsBelow]) (Nat.le_refl _)
  rintro xs entry ⟨hlen, hp, same⟩
  subst entry
  exact called xs original ⟨rfl, hlen, hp.enter_params, rfl, rfl, rfl⟩

/-- Native functional verification recovers the existing caller postcondition.
No instruction budget or callee-register restoration proof is required here. -/
theorem call_total_contract {base scratch : Word w} {xs : List (Word w)} (dst : Reg)
    (hw : 2 ≤ w) (lookup : functions[selfFn]? = some (function selfFn)) :
    TotalRelContract functions heapLimit (Nat.clog 2 xs.length + 1)
      (.call dst selfFn [.var 0, .var 1, .var 2])
      (Pre heapLimit base scratch xs)
      (fun entry finish => Post heapLimit base scratch xs entry finish ∧
        (∀ r, r ≠ dst → finish.regs r = entry.regs r) ∧ finish.regs dst = 0) := by
  intro entry hp
  have specified := (call_stateM_refines (heapLimit := heapLimit) (base := base) (scratch := scratch)
    xs.length entry dst hw lookup).stateM_spec_refines (sortState_spec xs)
  apply Verification.TotalWP.of_contract (specified xs) ⟨⟨rfl, hp, rfl⟩, rfl⟩
  rintro finish ⟨⟨zero, shared, locals⟩, sortedResult⟩
  refine ⟨?_, locals, zero⟩
  rw [sortedResult] at shared
  exact ⟨shared.1, shared.2.1, shared.2.2.1, shared.2.2.2.1, shared.2.2.2.2⟩

end Ram.Source.Array.MergeSort
