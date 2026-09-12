/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Cons
import Complexity.Language.List.Uncons
import Complexity.Language.Syntax
import Complexity.Language.Syntax.Represented
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Std.Tactic.Do

/-!
# Native linked-list programs and named node operations

The author writes one optional-root match and one `ref.read`. The generated
source body is definitionally the public linked-list operation, so its existing
mathematical contract and refinement apply directly. The generated `uncons_eq`
observes the same read through `NodeRef.readM`; no host list traversal or second
machine proof supplies its behavior. Construction similarly writes one
`NodeRef.cons`, reuses the public cons contract, and retains the exact new heap
and fresh root. A singleton demonstrates inference of an absent tail's type.

The native family accepts ordinary `List Nat` arguments. One declaration
generates a mathematical function and an actual node-backed source function;
its refinement is generated without an author-written traversal proof.
Constant initial values, reordered parameters, consecutive folds and calls to
earlier native functions use the same correspondence construction. Mathematical
sum proofs use existing List algebra and do not mention source environments.

`NativeConstruction` also returns ordinary lists. Its generated source allocates
real nodes, shares tails and composes calls at their actual intermediate heaps.
The mathematical proofs remain ordinary list equations; the final consumer
observes both an old list and its new extension after allocation.
-/

namespace Complexity.Language.Examples.LinkedList

open scoped Std.Do Part.TotalCorrectness

source_program (pure) Reducer where
  def add (accumulator : Nat) (head : Nat) : Nat := do
    return accumulator + head

/-- A named fold callback is an ordinary mathematical function generated from
the same source body as its executable implementation. -/
theorem add_eq (accumulator head : Nat) :
    Reducer.add accumulator head = accumulator + head := rfl

source_program Implementation where
  def uncons (root : Option (NodeRef Nat)) : Option (Nat × Option (NodeRef Nat)) := do
    match root with
    | none => return none
    | some ref =>
      let fields ← ref.read
      return some fields

/-- The high-level declaration generates exactly the already verified source body. -/
theorem uncons_body_eq : Implementation.unconsBody = List.Uncons.body .nat := rfl

/-- The public operation's contract applies without another implementation proof. -/
theorem uncons_total (values : List Nat) :
    Implementation.uncons_contract
      (fun root heap => (Representation.list .nat).Rel values root heap)
      (fun _ initial result finish =>
        (List.Uncons.resultRepresentation .nat).Rel
          (values.head?.map (fun head => (head, values.tail))) result finish ∧ finish = initial) :=
  List.Uncons.total .nat values

/-- Ordinary List decomposition refines the same named source declaration. -/
theorem uncons_refines :
    RepresentedFunction.Refines Implementation.program Implementation.unconsId
      (List.Uncons.representation .nat) (fun _ => True)
      (fun values => values.head?.map (fun head => (head, values.tail))) :=
  List.Uncons.refines .nat

/-- The native action returns the ordinary head/tail view and preserves the
entire initial heap, including other roots sharing this list's tail. -/
theorem uncons_spec (root : Option (NodeRef .nat)) (values : List Nat) (initial : Heap) :
    ⦃fun heap => ⌜heap = initial ∧ (Representation.list .nat).Rel values root heap⌝⦄
      Implementation.uncons root
    ⦃⇓ result finish => ⌜(List.Uncons.resultRepresentation .nat).Rel
      (values.head?.map (fun head => (head, values.tail))) result finish ∧ finish = initial⌝⦄ := by
  apply (triple_iff_eval _ _ _).mpr
  rintro heap ⟨same, observed⟩
  subst heap
  exact (Implementation.uncons_total_iff _ _).mp (uncons_total values) root initial observed

source_program Construction where
  def cons (head : Nat) (tail : Option (NodeRef Nat)) : Option (NodeRef Nat) := do
    let ref ← NodeRef.cons head tail
    return some ref

/-- Named construction generates exactly the existing public cons operation. -/
theorem cons_body_eq : Construction.consBody = List.Cons.body .nat := rfl

/-- The public contract supplies mathematical cons, the exact allocated heap
and fresh root, and preservation of every old represented list. -/
theorem cons_total (values : List Nat) :
    Construction.cons_contract
      (fun _ tail heap => (Representation.list .nat).Rel values tail heap)
      (fun head tail initial result finish =>
        (Representation.list .nat).Rel (head :: values) result finish ∧
        finish = (initial.cons head tail).2 ∧
        result = some (initial.cons head tail).1 ∧ initial.ShapeExtends finish) := by
  intro args heap observed
  exact List.Cons.total .nat args.head values args heap ⟨rfl, observed⟩

/-- The same named constructor refines ordinary mathematical `List.cons`. -/
theorem cons_refines :
    RepresentedFunction.Refines Construction.program Construction.consId
      (List.Cons.representation .nat) (fun _ => True)
      (fun input => input.1 :: input.2) :=
  List.Cons.refines .nat

/-- The native action inherits the public source contract without reproving
allocation or the representation of the shared tail. -/
theorem cons_spec (head : Nat) (tail : Option (NodeRef .nat))
    (values : List Nat) (initial : Heap) :
    ⦃fun heap => ⌜heap = initial ∧ (Representation.list .nat).Rel values tail heap⌝⦄
      Construction.cons head tail
    ⦃⇓ result finish => ⌜(Representation.list .nat).Rel (head :: values) result finish ∧
      finish = (initial.cons head tail).2 ∧
      result = some (initial.cons head tail).1 ∧ initial.ShapeExtends finish⌝⦄ := by
  apply (triple_iff_eval _ _ _).mpr
  rintro heap ⟨same, observed⟩
  subst heap
  exact (Construction.cons_total_iff _ _).mp (cons_total values) head tail initial observed

source_program Singleton where
  def singleton (head : Nat) : Option (NodeRef Nat) := do
    let ref ← NodeRef.cons head none
    return some ref

/-- The inferred absent tail is an ordinary typed primitive binding before
the real allocation, not an unchecked host-side list constructor. -/
theorem singleton_body_eq :
    Singleton.singletonBody =
      .letPrim (.none (.node .nat))
        (.consNode (.var (.there .here)) (.var .here)
          (.letPrim (.some (.var .here)) (.ret (.var .here)))) := rfl

/-- The generated observation equations identify singleton with cons of the
absent tail, even though their source argument lists differ. -/
theorem singleton_eq_cons (head : Nat) :
    Singleton.singleton head = Construction.cons head none := by
  rw [Singleton.singleton_eq, Construction.cons_eq]

/-- The singleton has the ordinary `[head]` contract and allocates exactly
the same fresh node as the public constructor with an empty represented tail. -/
theorem singleton_total :
    Singleton.singleton_contract (fun _ _ => True)
      (fun head initial result finish =>
        (Representation.list .nat).Rel [head] result finish ∧
        finish = (initial.cons (τ := .nat) head none).2 ∧
        result = some (initial.cons (τ := .nat) head none).1 ∧ initial.ShapeExtends finish) := by
  apply (Singleton.singleton_total_iff _ _).mpr
  intro head heap _
  rw [singleton_eq_cons]
  exact (Construction.cons_total_iff _ _).mp (cons_total []) head none heap
    (Representation.list_nil .nat heap)

source_program (native) Native importing Reducer where
  def sumFrom (values : List Nat) (initial : Nat) : Nat := do
    let result := values.foldl Reducer.add initial
    return result

  def sum (values : List Nat) : Nat := do
    let result := List.foldl Reducer.add 0 values
    return result

  def sumPair (left : List Nat) (initial : Nat) (right : List Nat) : Nat := do
    let start := initial + 0
    let first := left.foldl Reducer.add start
    let result := right.foldl Reducer.add first
    return result

  def sumTwice (values : List Nat) : Nat := do
    let first := sum values
    let result := sumFrom values first
    return result

/-- The mathematical proof uses ordinary list algebra. The native frontend
generates the correspondence to the actual linked traversal separately. -/
theorem sumFrom_eq (values : List Nat) (initial : Nat) :
    Native.sumFrom values initial = initial + values.sum := by
  change values.foldl (· + ·) initial = initial + values.sum
  simpa only [Nat.add_zero, ← List.sum_eq_foldl] using
    (List.foldl_assoc (op := ((· + ·) : Nat → Nat → Nat))
      (l := values) (a₁ := initial) (a₂ := 0))

/-- A constant initial value needs no represented argument supplied by the user. -/
theorem sum_eq (values : List Nat) : Native.sum values = values.sum := by
  change Native.sumFrom values 0 = values.sum
  simp only [sumFrom_eq, Nat.zero_add]

/-- Consecutive traversals can observe lists with shared tails: their abstract
correctness needs no heap-disjointness assumption or repeated loop proof. -/
theorem sumPair_eq (left right : List Nat) (initial : Nat) :
    Native.sumPair left initial right = initial + left.sum + right.sum := by
  change Native.sumFrom right (Native.sumFrom left initial) = _
  rw [sumFrom_eq, sumFrom_eq]

/-- Calls to earlier functions in the same native family reuse their generated
correspondence while the mathematical proof remains ordinary rewriting. -/
theorem sumTwice_eq (values : List Nat) :
    Native.sumTwice values = values.sum + values.sum := by
  change Native.sumFrom values (Native.sum values) = _
  rw [sumFrom_eq, sum_eq]

/-- An ordinary mathematical theorem specializes the generated refinement of
the very same source declaration; no environment or register adapter is supplied. -/
theorem sum_correct :
    RepresentedFunction.Total Native.program Native.sumId Native.sum_representation
      (fun _ => True) (fun values result => result = values.sum) :=
  Native.sum_refines.of_math (fun values _ => sum_eq values)

source_program (native) NativeConstruction importing Reducer where
  def prepend (head : Nat) (values : List Nat) : List Nat := do
    let result := head :: values
    return result

  def singleton (head : Nat) : List Nat := do
    let result := List.cons head ([] : List Nat)
    return result

  def prependPair (first : Nat) (second : Nat) (values : List Nat) : List Nat := do
    let tail := prepend second values
    let result := prepend first tail
    return result

  def sumWithPrepended (head : Nat) (values : List Nat) : Nat := do
    let grown := prepend head values
    let original := values.foldl Reducer.add 0
    let result := grown.foldl Reducer.add original
    return result

/-- The native result is an ordinary list; its implementation allocates one
node and shares the supplied tail through the generated correspondence. -/
theorem prepend_eq (head : Nat) (values : List Nat) :
    NativeConstruction.prepend head values = head :: values := rfl

/-- An empty list is represented without storage, so singleton needs just the
actual cons operation selected by the same native declaration. -/
theorem singleton_eq (head : Nat) : NativeConstruction.singleton head = [head] := rfl

/-- Calls returning lists compose with ordinary equations, without a second
implementation or a user-written proof about intermediate heaps. -/
theorem prependPair_eq (first second : Nat) (values : List Nat) :
    NativeConstruction.prependPair first second values = first :: second :: values := rfl

/-- Both the old list and the freshly extended list are available after
allocation. Their source representations are composed by the frontend. -/
theorem sumWithPrepended_eq (head : Nat) (values : List Nat) :
    NativeConstruction.sumWithPrepended head values = values.sum + (head :: values).sum := by
  change Native.sumFrom (head :: values) (Native.sumFrom values 0) = _
  rw [sumFrom_eq, sumFrom_eq]
  simp only [Nat.zero_add]

/-- Ordinary mathematics specializes the generated relation with the actual
returned list in its final heap. No time, capacity or disjointness premise is needed. -/
theorem prependPair_correct :
    RepresentedFunction.Total NativeConstruction.program NativeConstruction.prependPairId
      NativeConstruction.prependPair_representation (fun _ => True)
      (fun input result => result = input.1 :: input.2.1 :: input.2.2) :=
  NativeConstruction.prependPair_refines.of_math
    (fun input _ => prependPair_eq input.1 input.2.1 input.2.2)

source_program (native) ListReducer where
  def push (accumulator : List Nat) (head : Nat) : List Nat := do
    let result := head :: accumulator
    return result

source_program (native) NativeLists importing ListReducer, Reducer where
  def reverseAppend (values : List Nat) (tail : List Nat) : List Nat := do
    let result := values.foldl ListReducer.push tail
    return result

  def reverse (values : List Nat) : List Nat := do
    let result := reverseAppend values ([] : List Nat)
    return result

  def reverseWithHead (values : List Nat) (head : Nat) (tail : List Nat) : List Nat := do
    let seeded := ListReducer.push tail head
    let result := values.foldl ListReducer.push seeded
    return result

  def reverseSum (values : List Nat) : Nat := do
    let reversed := reverse values
    let result := reversed.foldl Reducer.add 0
    return result

/-- An imported allocating callback is still an ordinary mathematical function;
its generated source implementation constructs the real shared-tail node. -/
theorem push_eq (accumulator : List Nat) (head : Nat) :
    ListReducer.push accumulator head = head :: accumulator := rfl

/-- The author's proof reuses Lean's existing fold/cons identity. The frontend
supplies callback correspondence, traversal termination and final-heap transport. -/
theorem reverseAppend_eq (values tail : List Nat) :
    NativeLists.reverseAppend values tail = values.reverse ++ tail := by
  change values.foldl (fun accumulator head => head :: accumulator) tail = _
  exact List.foldl_flip_cons_eq_append'

/-- Returning the result of the same allocating traversal specializes its
ordinary mathematical equation; no source-heap induction is repeated. -/
theorem reverse_eq (values : List Nat) : NativeLists.reverse values = values.reverse := by
  change NativeLists.reverseAppend values [] = _
  simp only [reverseAppend_eq, List.append_nil]

/-- A direct imported call and a fold of that same callback compose with their
actual intermediate heap while the public proof uses ordinary List operations. -/
theorem reverseWithHead_eq (values : List Nat) (head : Nat) (tail : List Nat) :
    NativeLists.reverseWithHead values head tail = values.reverse ++ head :: tail := by
  change NativeLists.reverseAppend values (ListReducer.push tail head) = _
  rw [reverseAppend_eq, push_eq]

/-- A scalar fold can consume the newly allocated list from an earlier call. -/
theorem reverseSum_eq (values : List Nat) : NativeLists.reverseSum values = values.sum := by
  change Native.sumFrom (NativeLists.reverse values) 0 = _
  rw [sumFrom_eq, reverse_eq, List.sum_reverse]
  exact Nat.zero_add _

/-- The mathematical reverse/append theorem describes the actual returned list
in the final heap, with no machine budget or input-list separation premise. -/
theorem reverseAppend_correct :
    RepresentedFunction.Total NativeLists.program NativeLists.reverseAppendId
      NativeLists.reverseAppend_representation (fun _ => True)
      (fun input result => result = input.1.reverse ++ input.2) :=
  NativeLists.reverseAppend_refines.of_math
    (fun input _ => reverseAppend_eq input.1 input.2)

source_program (native) NativeBranches importing NativeConstruction, Reducer where
  def choosePrepend (flag : Bool) (head : Nat) (left : List Nat) (right : List Nat) :
      List Nat := do
    let chosen : List Nat ← if flag then do
      let grown := head :: left
      let selected := NativeConstruction.prepend head grown
      return selected
    else do
      let selected := NativeConstruction.prepend head right
      return selected
    let result := NativeConstruction.prepend head chosen
    return result

  def chooseSum (flag : Bool) (head : Nat) (left : List Nat) (right : List Nat) : Nat := do
    let chosen : List Nat ← if flag then do
      let selected := head :: left
      return selected
    else do
      let selected := NativeConstruction.prepend head right
      return selected
    let result := chosen.foldl Reducer.add 0
    return result

/-- The selected branch returns an ordinary list to one common continuation.
Only the true branch adds the extra prefix node before the two named calls. -/
theorem choosePrepend_eq (flag : Bool) (head : Nat) (left right : List Nat) :
    NativeBranches.choosePrepend flag head left right =
      head :: head :: (if flag then head :: left else right) := by
  cases flag <;> rfl

/-- A scalar fold consumes the list produced by either allocating branch.
The proof is ordinary sum algebra, without an intermediate-heap induction. -/
theorem chooseSum_eq (flag : Bool) (head : Nat) (left right : List Nat) :
    NativeBranches.chooseSum flag head left right =
      head + (if flag then left.sum else right.sum) := by
  cases flag with
  | false =>
      change Native.sumFrom (head :: right) 0 = head + right.sum
      simp only [sumFrom_eq, List.sum_cons, Nat.zero_add]
  | true =>
      change Native.sumFrom (head :: left) 0 = head + left.sum
      simp only [sumFrom_eq, List.sum_cons, Nat.zero_add]

/-- The generated correspondence relates the actual selected branch and its
common continuation to the ordinary list equation in the actual final heap. -/
theorem choosePrepend_correct :
    RepresentedFunction.Total NativeBranches.program NativeBranches.choosePrependId
      NativeBranches.choosePrepend_representation (fun _ => True)
      (fun input result => result = input.2.1 :: input.2.1 ::
        (if input.1 then input.2.1 :: input.2.2.1 else input.2.2.2)) :=
  NativeBranches.choosePrepend_refines.of_math
    (fun input _ => choosePrepend_eq input.1 input.2.1 input.2.2.1 input.2.2.2)

/-- List-valued branch merging and a subsequent scalar fold share the same
generated source refinement; no separate source traversal is supplied. -/
theorem chooseSum_correct :
    RepresentedFunction.Total NativeBranches.program NativeBranches.chooseSumId
      NativeBranches.chooseSum_representation (fun _ => True)
      (fun input result => result = input.2.1 +
        (if input.1 then input.2.2.1.sum else input.2.2.2.sum)) :=
  NativeBranches.chooseSum_refines.of_math
    (fun input _ => chooseSum_eq input.1 input.2.1 input.2.2.1 input.2.2.2)

source_program (native) NativeViews importing NativeConstruction where
  def uncons (values : List Nat) : Option (Nat × List Nat) := do
    let result := values.uncons
    return result

  def consPair (fields : Nat × List Nat) : List Nat := do
    let result := NativeConstruction.prepend fields.1 fields.2
    return result

  def restoreOr (parts : Option (Nat × List Nat)) (fallback : List Nat) : List Nat := do
    let result : List Nat ← match parts with
      | none => do
        return fallback
      | some fields => do
        let restored := consPair fields
        return restored
    return result

  def inspectAndPrepend (head : Nat) (values : List Nat) :
      Option (Nat × List Nat) × List Nat := do
    let parts := values.uncons
    let grown := NativeConstruction.prepend head values
    return (parts, grown)

  def replaceHead (replacement : Nat) (values : List Nat) : List Nat := do
    let tail : List Nat ← match values with
      | [] => do
        return ([] : List Nat)
      | _head :: rest => do
        return rest
    let result := NativeConstruction.prepend replacement tail
    return result

/-- The optional mathematical head and tail describe the actual node read. -/
theorem nativeUncons_eq (values : List Nat) :
    NativeViews.uncons values = values.head?.map (fun head => (head, values.tail)) := rfl

/-- A compound argument retains the ordinary head and its shared List tail. -/
theorem consPair_eq (fields : Nat × List Nat) :
    NativeViews.consPair fields = fields.1 :: fields.2 := rfl

/-- Optional represented fields can be matched and passed to a named constructor. -/
theorem restoreOr_eq (parts : Option (Nat × List Nat)) (fallback : List Nat) :
    NativeViews.restoreOr parts fallback =
      (match parts with | none => fallback | some fields => fields.1 :: fields.2) := by
  cases parts <;> rfl

/-- The old compound observation survives an actual allocation, and both old
fields and the newly constructed list are returned together. -/
theorem inspectAndPrepend_eq (head : Nat) (values : List Nat) :
    NativeViews.inspectAndPrepend head values =
      (values.head?.map (fun value => (value, values.tail)), head :: values) := rfl

/-- List cases expose the ordinary tail; the common continuation constructs
the new first node. This is a mathematical proof, not a source-heap induction. -/
theorem replaceHead_eq (replacement : Nat) (values : List Nat) :
    NativeViews.replaceHead replacement values = replacement :: values.tail := by
  cases values <;> rfl

/-- Automatically generated correspondence retains both parts of the compound
result at the same final heap, including the pre-allocation head/tail view. -/
theorem inspectAndPrepend_correct :
    RepresentedFunction.Total NativeViews.program NativeViews.inspectAndPrependId
      NativeViews.inspectAndPrepend_representation (fun _ => True)
      (fun input result => result =
        (input.2.head?.map (fun head => (head, input.2.tail)), input.1 :: input.2)) :=
  NativeViews.inspectAndPrepend_refines.of_math
    (fun input _ => inspectAndPrepend_eq input.1 input.2)

/-- The List-match implementation inherits its ordinary functional theorem
without any word-width, storage or time-budget assumption. -/
theorem replaceHead_correct :
    RepresentedFunction.Total NativeViews.program NativeViews.replaceHeadId
      NativeViews.replaceHead_representation (fun _ => True)
      (fun input result => result = input.1 :: input.2.tail) :=
  NativeViews.replaceHead_refines.of_math
    (fun input _ => replaceHead_eq input.1 input.2)

end Complexity.Language.Examples.LinkedList
