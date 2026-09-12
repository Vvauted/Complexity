/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Representation
import Complexity.Language.Eval.Verification
import Complexity.Language.Verification

/-!
# Mathematical contracts on represented source arguments and results

Argument representations compose the value relations of `Representation` without
requiring clients to project the source environment. A `FunctionRepresentation`
also observes the actual final heap and may observe an original argument instead
of the returned value. Thus an in-place function returning `Unit` can expose a
mathematical array result without pretending to allocate or freeze that array.

`RepresentedFunction.Total` is a call contract: it applies to every actual input
representation in every initial heap. It neither constructs those inputs nor
asserts that every mathematical input has a representation. Its successful
termination claim is independent of machine capacity and instruction budgets.

`RepresentedFunction.Refines` requires a proved correspondence with one ordinary
mathematical function. `Refines.of_math` combines that correspondence with a
mathematical theorem; correctness of an unrelated function cannot supply the
correspondence. Both interfaces use the existing `FunctionTotal` semantics.
-/

namespace Complexity.Language

universe u v

/-- A mathematical observation of the actual typed argument environment.
Different arguments may share storage; no disjointness is implicit. -/
structure ArgumentRepresentation (α : Type u) (Γ : List Ty) where
  Rel : α → Env Γ → Heap → Prop
  functional : ∀ {a b args heap}, Rel a args heap → Rel b args heap → a = b

namespace ArgumentRepresentation

/-- A pure argument encoding, with equality interpreted in the existing typed
environment. The encoding is mathematical transport, not a runtime loader. -/
def ofEmbedding {α : Type u} {Γ : List Ty} (encoding : α ↪ Env Γ) :
    ArgumentRepresentation α Γ where
  Rel input args _ := encoding input = args
  functional first second := encoding.injective (first.trans second.symm)

@[simp] theorem ofEmbedding_rel {α : Type u} {Γ : List Ty}
    (encoding : α ↪ Env Γ) (input : α) (args : Env Γ) (heap : Heap) :
    (ofEmbedding encoding).Rel input args heap ↔ encoding input = args := Iff.rfl

/-- The empty argument list carries no mathematical input data. -/
def nil : ArgumentRepresentation Unit [] where
  Rel _ _ _ := True
  functional _ _ := Subsingleton.elim _ _

/-- Observe one argument and the remaining arguments in the same actual heap. -/
def cons {α : Type u} {β : Type v} {τ : Ty} {Γ : List Ty}
    (head : Representation α τ) (tail : ArgumentRepresentation β Γ) :
    ArgumentRepresentation (α × β) (τ :: Γ) where
  Rel input args heap := head.Rel input.1 args.head heap ∧ tail.Rel input.2 args.tail heap
  functional first second := Prod.ext (head.functional first.1 second.1)
    (tail.functional first.2 second.2)

/-- A single argument needs no user-visible trailing `Unit` coordinate. -/
def single {α : Type u} {τ : Ty} (value : Representation α τ) :
    ArgumentRepresentation α [τ] where
  Rel input args heap := value.Rel input args.head heap
  functional first second := value.functional first second

@[simp] theorem nil_rel (input : Unit) (args : Env []) (heap : Heap) :
    nil.Rel input args heap ↔ True := Iff.rfl

@[simp] theorem cons_rel {α : Type u} {β : Type v} {τ : Ty} {Γ : List Ty}
    (head : Representation α τ) (tail : ArgumentRepresentation β Γ)
    (input : α × β) (value : Value τ) (args : Env Γ) (heap : Heap) :
    (cons head tail).Rel input (Env.cons value args) heap ↔
      head.Rel input.1 value heap ∧ tail.Rel input.2 args heap := Iff.rfl

@[simp] theorem single_rel {α : Type u} {τ : Ty} (representation : Representation α τ)
    (input : α) (value : Value τ) (heap : Heap) :
    (single representation).Rel input (Env.cons value Env.empty) heap ↔
      representation.Rel input value heap := Iff.rfl

end ArgumentRepresentation

/-- Input and output observations of a fixed source signature. The output may
depend on the mathematical input, original arguments and both actual heaps.
This is an observation relation, not an executable encoder or decoder. -/
structure FunctionRepresentation (α : Type u) (β : α → Type v) (signature : Signature) where
  input : ArgumentRepresentation α signature.params
  post : (x : α) → Env signature.params → Heap → Value signature.result → Heap → β x → Prop
  post_functional : ∀ {x args initialHeap value finalHeap} {a b : β x},
    post x args initialHeap value finalHeap a → post x args initialHeap value finalHeap b → a = b

namespace FunctionRepresentation

/-- Observe the actual returned value using its representation in the final heap. -/
def ofResult {α : Type u} {β : α → Type v} {signature : Signature}
    (input : ArgumentRepresentation α signature.params)
    (result : (x : α) → Representation (β x) signature.result) :
    FunctionRepresentation α β signature where
  input := input
  post x _ _ value finalHeap output := (result x).Rel output value finalHeap
  post_functional first second := (result _).functional first second

/-- Native pure arguments and dependent results represented by checked
embeddings. This does not install either embedding as a machine instruction. -/
def ofEmbedding {α : Type u} {β : α → Type v} {signature : Signature}
    (input : α ↪ Env signature.params)
    (result : (x : α) → β x ↪ Value signature.result) :
    FunctionRepresentation α β signature :=
  ofResult (ArgumentRepresentation.ofEmbedding input)
    (fun x => Representation.ofEmbedding (result x))

/-- Observe an original argument in the actual final heap. In particular, an
in-place function need not return its borrowed buffer to expose updated contents.
The typed variable selects a source argument, never a machine register. -/
def ofArgument {α : Type u} {β : α → Type v} {signature : Signature} {τ : Ty}
    (input : ArgumentRepresentation α signature.params) (argument : Var signature.params τ)
    (result : (x : α) → Representation (β x) τ) :
    FunctionRepresentation α β signature where
  input := input
  post x args _ _ finalHeap output := (result x).Rel output (args.get argument) finalHeap
  post_functional first second := (result _).functional first second

end FunctionRepresentation

namespace RepresentedFunction

/-- Successful source execution for every actual representation satisfying the
mathematical precondition. No mathematical input is assumed representable. -/
def Total {α : Type u} {β : α → Type v} {signatures : List Signature}
    (program : Program signatures) (fn : Fin signatures.length)
    (representation : FunctionRepresentation α β signatures[fn])
    (pre : α → Prop) (post : (x : α) → β x → Prop) : Prop :=
  ∀ x, pre x → FunctionTotal program fn (representation.input.Rel x)
    (fun args initialHeap value finalHeap =>
      ∃ output, representation.post x args initialHeap value finalHeap output ∧ post x output)

/-- A proved implementation correspondence to an ordinary mathematical function.
It refers to the same source program as subsequent correctness and cost claims. -/
def Refines {α : Type u} {β : α → Type v} {signatures : List Signature}
    (program : Program signatures) (fn : Fin signatures.length)
    (representation : FunctionRepresentation α β signatures[fn])
    (pre : α → Prop) (function : (x : α) → β x) : Prop :=
  ∀ x, pre x → FunctionTotal program fn (representation.input.Rel x)
    (fun args initialHeap value finalHeap =>
      representation.post x args initialHeap value finalHeap (function x))

/-- Transport a represented contract through one complete signature equality.
The argument and final-heap observations remain those of the same representation;
clients need not eliminate an equality against a particular structured signature. -/
theorem Refines.cast_iff {α : Type u} {β : α → Type v}
    {table : List Signature} (source : Program table) (fn : Fin table.length)
    {selected : Signature} (same : selected = table[fn])
    (representation : FunctionRepresentation α β selected)
    (domain : α → Prop) (step : (input : α) → β input) :
    Refines source fn
      (cast (congrArg (FunctionRepresentation α β) same) representation) domain step ↔
      ∀ input, domain input → FunctionTotal source fn
        (cast (congrArg (fun s => Env s.params → Heap → Prop) same)
          (representation.input.Rel input))
        (cast (congrArg (fun s =>
          Env s.params → Heap → Value s.result → Heap → Prop) same)
          (fun args initial value finish =>
            representation.post input args initial value finish (step input))) := by
  cases same
  rfl

variable {α : Type u} {β : α → Type v} {signatures : List Signature}
variable {program : Program signatures} {fn : Fin signatures.length}
variable {representation : FunctionRepresentation α β signatures[fn]}
variable {pre pre' : α → Prop} {post post' : (x : α) → β x → Prop}

/-- Change the presentation of equivalent argument and result observations.
The actual source function and both heaps are unchanged. In particular, a
frontend can reuse a library contract without requiring the represented value
to have a unique encoding or a heap-independent inverse. -/
theorem Refines.congr_representation
    {other : FunctionRepresentation α β signatures[fn]} {function : (x : α) → β x}
    (refinement : Refines program fn representation pre function)
    (input : ∀ x args heap,
      other.input.Rel x args heap ↔ representation.input.Rel x args heap)
    (output : ∀ x args initialHeap value finalHeap result,
      representation.post x args initialHeap value finalHeap result ↔
        other.post x args initialHeap value finalHeap result) :
    Refines program fn other pre function := by
  intro x valid
  apply (refinement x valid).consequence
  · intro args heap represented
    exact (input x args heap).mp represented
  · intro args initialHeap value finalHeap _ represented
    exact (output x args initialHeap value finalHeap (function x)).mp represented

/-- Turn a checked encoded evaluation equation into a native mathematical
refinement. The equation must hold in every initial heap and for every input in
the stated domain; it cannot be supplied by evaluating only one selected input.
No inverse on invalid core values and no separate implementation proof is needed. -/
theorem Refines.of_encoded_eval
    (input : α ↪ Env signatures[fn].params)
    (output : (x : α) → β x ↪ Value signatures[fn].result)
    (function : (x : α) → β x)
    (correspondence : ∀ x, pre x → ∀ heap,
      program.eval fn (input x) heap = Part.some (.ok ((output x).toFun (function x)), heap)) :
    Refines program fn (FunctionRepresentation.ofEmbedding input output) pre function := by
  intro x valid
  apply FunctionTotal.iff_eval.mpr
  intro args heap represented
  have same : input x = args := represented
  subst args
  exact ⟨(output x).toFun (function x), heap, correspondence x valid heap, rfl⟩

/-- The action-equation form of `Refines.of_encoded_eval`, suitable for
automatically generated native/source correspondence theorems. -/
theorem Refines.of_encoded_eq_pure
    (input : α ↪ Env signatures[fn].params)
    (output : (x : α) → β x ↪ Value signatures[fn].result)
    (function : (x : α) → β x)
    (correspondence : ∀ x, pre x → program.eval fn (input x) =
      (pure ((output x).toFun (function x)) : ExceptT Fault (StateT Heap Part)
        (Value signatures[fn].result))) :
    Refines program fn (FunctionRepresentation.ofEmbedding input output) pre function :=
  Refines.of_encoded_eval input output function
    (fun x valid heap => congrFun (correspondence x valid) heap)

/-- Compose already proved representation correspondence with ordinary mathematics.
This does not infer correspondence from functional correctness alone. -/
theorem Refines.of_math {function : (x : α) → β x}
    (refinement : Refines program fn representation pre function)
    (mathematics : ∀ x, pre x → post x (function x)) :
    Total program fn representation pre post := by
  intro x valid
  apply (refinement x valid).consequence (fun _ _ represented => represented)
  intro args initialHeap value finalHeap _ represented
  exact ⟨function x, represented, mathematics x valid⟩

/-- Strengthen the mathematical domain or weaken the mathematical conclusion,
retaining the same input and output representation relations. -/
theorem Total.consequence (specification : Total program fn representation pre post)
    (input : ∀ x, pre' x → pre x)
    (output : ∀ x y, pre' x → post x y → post' x y) :
    Total program fn representation pre' post' := by
  intro x valid
  apply (specification x (input x valid)).consequence (fun _ _ represented => represented)
  rintro args initialHeap value finalHeap _ ⟨y, represented, property⟩
  exact ⟨y, represented, output x y valid property⟩

/-- Transfer the high-level result to any actual successful evaluation of the
same represented invocation, rather than selecting another execution witness. -/
theorem Total.post_of_eval (specification : Total program fn representation pre post)
    {x : α} (valid : pre x) {args : Env signatures[fn].params} {initialHeap finalHeap : Heap}
    {value : Value signatures[fn].result}
    (represented : representation.input.Rel x args initialHeap)
    (evaluated : program.eval fn args initialHeap = Part.some (.ok value, finalHeap)) :
    ∃ output, representation.post x args initialHeap value finalHeap output ∧ post x output := by
  obtain ⟨finish, execution, sameHeap⟩ := Program.eval_eq_ok_iff.mp evaluated
  simpa only [sameHeap] using (specification x valid).postcondition represented execution

end RepresentedFunction

end Complexity.Language
