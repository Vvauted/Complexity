/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Basic
import Complexity.Language.Linking.Extension
import Complexity.Language.Linking.Verification

/-!
# Executable packing at a mathematical program's entry

The fixed `Program.Input` layout may supply separate arguments while a native
source function accepts one structured value. `Packing` describes only finite
structural assembly using existing atoms and pairs. Its `call` expands to real
source `letPrim`, `call` and `ret` statements; `ofPacking` installs these in a new
entry function, retaining the original bodies through `Program.extend`.

The contract bridge reuses the original function's successful execution and
actual final heap. It changes neither the preloaded input convention nor the
output observation. In particular this is not host-side preprocessing, a new
evaluator, or a free runtime conversion. Resource proofs must account for this
entry's emitted instructions and its additional call frame.
-/

namespace Complexity.Program

open Language

/-- Finite structural assembly in administrative normal form. A pair binds an
actual primitive result for its continuation; `done` selects the final atom.
Only existing source atoms and product construction are available. -/
inductive Packing : List Ty → Ty → Type where
  | done {Γ : List Ty} {τ : Ty} : Atom Γ τ → Packing Γ τ
  | pair {Γ : List Ty} {left right τ : Ty} :
      Atom Γ left → Atom Γ right → Packing (.prod left right :: Γ) τ → Packing Γ τ

namespace Packing

/-- The value assembled from the supplied source locals. This mathematical
observation describes the corresponding source primitives, not free execution. -/
@[simp] def eval : {Γ : List Ty} → {τ : Ty} → Packing Γ τ → Env Γ → Value τ
  | _, _, .done value, args => value.eval args
  | _, _, .pair left right rest, args =>
      rest.eval (Env.cons (left.eval args, right.eval args) args)

/-- Call an existing single-argument function after executing the structural
assembly. The return preserves the callee's actual result and final heap. -/
def call {signatures : List Signature} {τ result : Ty}
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩) :
    {Γ : List Ty} → Packing Γ τ → Stmt signatures Γ result
  | _, .done value =>
      Stmt.callOfEq fn same (.cons value .nil) (.ret (.var .here))
  | _, .pair left right rest => .letPrim (.pair left right) (rest.call fn same)

/-- Structural assembly followed by a real call inherits the callee's contract.
The postcondition observes the assembled input and the actual initial/final
heaps; correctness and termination require no proposed resource bound. -/
theorem call_total {signatures : List Signature} {program : Language.Program signatures}
    {τ result : Ty} (fn : Fin signatures.length)
    (same : signatures[fn] = ⟨[τ], result⟩)
    {pre : Env [τ] → Heap → Prop}
    {post : Env [τ] → Heap → Value result → Heap → Prop}
    (callee : FunctionTotal program fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm) post))
    {Γ : List Ty} (packing : Packing Γ τ) (entry : State Γ)
    (input : pre (Env.cons (packing.eval entry.locals) Env.empty) entry.heap) :
    TotalWP program (packing.call fn same) (fun _ => False)
      (fun value finish =>
        post (Env.cons (packing.eval entry.locals) Env.empty) entry.heap value finish.heap)
      entry := by
  induction packing with
  | done value =>
      apply TotalWP.callOfEq (args := .cons value .nil)
        (continuation := .ret (.var .here)) (entry := entry) same callee input
      intro value heap property
      exact (TotalWP.ret_iff (.var .here)).mpr property
  | @pair Γ leftType rightType τ left right rest ih =>
      exact TotalWP.letPrim (ih same callee
        (State.cons (τ := .prod leftType rightType)
          (left.eval entry.locals, right.eval entry.locals) entry) input)

/-- Signature of the real entry added in front of the original source table. -/
def signature (Γ : List Ty) (result : Ty) : Signature := ⟨Γ, result⟩

/-- The actual new body is structural packing followed by a relocated call. -/
def bodies {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    (packing : Packing Γ τ) (fn : Fin signatures.length)
    (same : signatures[fn] = ⟨[τ], result⟩)
    (index : Fin [signature Γ result].length) :
    Stmt ([signature Γ result] ++ signatures)
      [signature Γ result][index].params [signature Γ result][index].result := by
  have zero : index = ⟨0, Nat.zero_lt_one⟩ := by
    apply Fin.ext
    exact Nat.lt_one_iff.mp index.isLt
  subst index
  exact packing.call (SignatureMap.appendRight [signature Γ result] signatures |>.toFun fn)
    ((SignatureMap.appendRight [signature Γ result] signatures |>.signature_eq fn).trans same)

/-- Add the executable packing entry while retaining all original source bodies
and their call graph through the checked source-table embedding. -/
def program {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩) :
    Language.Program ([signature Γ result] ++ signatures) :=
  source.extend [signature Γ result] (packing.bodies fn same)

/-- The packing entry is the first actual function of the extended table. -/
def entry (Γ : List Ty) (result : Ty) (signatures : List Signature) :
    Fin ([signature Γ result] ++ signatures).length :=
  ⟨0, Nat.zero_lt_succ _⟩

/-- The added entry has exactly the original preloaded argument layout. -/
@[simp] theorem entry_signature (Γ : List Ty) (result : Ty) (signatures : List Signature) :
    ([signature Γ result] ++ signatures)[entry Γ result signatures] = ⟨Γ, result⟩ := rfl

/-- The source entry is the supplied structural assembly and real call, not a
mathematical replacement for the selected implementation. -/
theorem body_entry {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩) :
    (SignatureMap.appendLeft [signature Γ result] signatures).body
      (packing.program source fn same) ⟨0, Nat.zero_lt_one⟩ =
      packing.bodies fn same ⟨0, Nat.zero_lt_one⟩ :=
  source.extend_body [signature Γ result] (packing.bodies fn same) ⟨0, Nat.zero_lt_one⟩

/-- Lift a source contract through the real added entry. All heaps and returned
values are those of the original call; only its argument structure is assembled. -/
theorem program_total {signatures : List Signature} {Γ : List Ty} {τ result : Ty}
    (packing : Packing Γ τ) (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], result⟩)
    {pre : Env [τ] → Heap → Prop}
    {post : Env [τ] → Heap → Value result → Heap → Prop}
    (callee : FunctionTotal source fn
      (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm) pre)
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop) same.symm) post)) :
    FunctionTotal (packing.program source fn same) (entry Γ result signatures)
      (cast (congrArg (fun s => Env s.params → Heap → Prop)
        (entry_signature Γ result signatures).symm)
        (fun args heap => pre (Env.cons (packing.eval args) Env.empty) heap))
      (cast (congrArg (fun s =>
        Env s.params → Heap → Value s.result → Heap → Prop)
        (entry_signature Γ result signatures).symm)
        (fun args initial value finish =>
          post (Env.cons (packing.eval args) Env.empty) initial value finish)) := by
  apply (FunctionTotal.cast_iff _ _ (entry_signature Γ result signatures) _ _).mpr
  intro args heap input
  have relocated := FunctionTotal.renameCalls
    (source.embeds_extend [signature Γ result] (packing.bodies fn same)) callee
  have verified := packing.call_total
    (SignatureMap.appendRight [signature Γ result] signatures |>.toFun fn)
    ((SignatureMap.appendRight [signature Γ result] signatures |>.signature_eq fn).trans same)
    (pre := pre) (post := post)
    (by simpa only [cast_cast] using relocated) ⟨args, heap⟩ input
  obtain ⟨finish, control, executed, property⟩ := verified
  cases control with
  | normal => exact False.elim property
  | fault _ => exact False.elim property
  | returned value =>
      refine ⟨finish, value, ?_, property⟩
      change Exec _ ((SignatureMap.appendLeft [signature Γ result] signatures).body
        (packing.program source fn same) ⟨0, Nat.zero_lt_one⟩) _ _ _
      rw [body_entry]
      exact executed

end Packing

universe u v

/-- Expose a single structured source argument through the fixed mathematical
input's existing layout, by installing a real source packing entry. -/
def ofPacking {α : Type u} {β : Type v} [Input α] [Output β]
    {signatures : List Signature} {τ : Ty} (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], Output.type β⟩)
    (packing : Packing (Input.params α) τ) : Complexity.Program α β :=
  ofProgram (packing.program source fn same)
    (Packing.entry (Input.params α) (Output.type β) signatures)
    (Packing.entry_signature (Input.params α) (Output.type β) signatures)

/-- Publish ordinary mathematical correctness from the original native/source
refinement, using the real packing entry. The input compatibility proof concerns
the fixed preloaded values; it is not executable host preprocessing. The output
representation is exactly the interface's fixed observation at the final heap. -/
theorem Correct.of_packing_refines {α : Type u} {β : Type v} [Input α] [Output β]
    {signatures : List Signature} {τ : Ty} (source : Language.Program signatures)
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[τ], Output.type β⟩)
    (packing : Packing (Input.params α) τ) (inputRepresentation : Representation α τ)
    {valid : α → Prop} {post : α → β → Prop} {function : α → β}
    (refinement : RepresentedFunction.Refines source fn
      (cast (congrArg (FunctionRepresentation α (fun _ => β)) same.symm)
        (FunctionRepresentation.ofResult (ArgumentRepresentation.single inputRepresentation)
          (fun _ => Output.representation (β := β)))) valid function)
    (input : ∀ x, valid x →
      inputRepresentation.Rel x (packing.eval (Input.args x)) (Input.heap x))
    (mathematics : ∀ x, valid x → post x (function x)) :
    (ofPacking source fn same packing).Correct valid post := by
  intro x legal
  have callee := (RepresentedFunction.Refines.cast_iff source fn same.symm
    (FunctionRepresentation.ofResult (ArgumentRepresentation.single inputRepresentation)
      (fun _ => Output.representation (β := β))) valid function).mp refinement x legal
  have wrapped := packing.program_total source fn same callee
  obtain ⟨value, heap, evaluated, observed⟩ :=
    FunctionTotal.iff_eval.mp wrapped (Input.args x) (Input.heap x) (input x legal)
  exact ⟨function x, ⟨value, heap, evaluated, observed⟩, mathematics x legal⟩

end Complexity.Program
