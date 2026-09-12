/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Buffer.Copy
import Complexity.Language.Linking.Verification

/-!
# Mapping a buffer through a statically selected source function

The builders in `Buffer.Map` specialize a traversal to an actual function-table
entry. Each iteration reads the current source cell, executes that function's
body through `Stmt.callOfEq`, and writes the returned cell. The mathematical
function in the correctness contract is not an executable primitive.

Input and output cell kinds may differ. The mapper's `FunctionTotal` contract
must preserve old heap contents, including the input and the partially filled
output; it may allocate fresh temporary objects. The traversal and fresh-result
proofs reuse `Buffer.Contents`, the shared copying-prefix lemmas and `Array.map`.
These are typed-core builders for frontend specialization, not dynamic closures
or a second evaluator. Their ordinary source statements use the existing
compiler and retain the actual cost of every callee invocation.
-/

namespace Complexity.Language

namespace Buffer.Map

variable {signatures : List Signature} {inputKind outputKind : CellTy}

/-- The actual scalar function called once for each input cell. -/
def signature (inputKind outputKind : CellTy) : Signature :=
  ⟨[inputKind.toTy], outputKind.toTy⟩

/-- A mathematical mapper contract on an actual source function. Heap framing
is explicit: returning the right scalar alone does not protect the traversal. -/
def Contract (program : Program signatures) (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    (f : CellValue inputKind → CellValue outputKind) : Prop :=
  FunctionTotal program fn
    (cast (congrArg (fun s => Env s.params → Heap → Prop) same.symm)
      (fun _ _ => True))
    (cast (congrArg (fun s =>
      Env s.params → Heap → Value s.result → Heap → Prop) same.symm)
      (fun args initial value finish =>
        value = outputKind.toValue (f (inputKind.ofValue args.head)) ∧
          PreservesContents initial finish))

/-- One real read, selected source call and write, followed by cursor advance.
Only the fresh cursor is assigned; the enclosing caller locals are retained. -/
def iteration {Γ : List Ty} {result : Ty} (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind)) :
    Stmt signatures (.nat :: Γ) result :=
  .read (.var (.there source)) (.var .here)
    (Stmt.callOfEq fn same (.cons (.var .here) .nil)
      (.seq
        (.write (.var (.there (.there (.there target))))
          (.var (.there (.there .here))) (.var .here))
        (.assign (.there (.there .here))
          (.add (.var (.there (.there .here))) (.nat 1)))))

/-- The current index is compared with the source view's mathematical length. -/
def guard {Γ : List Ty} (source : Var Γ (.buffer inputKind)) :
    Stmt signatures (.nat :: Γ) .bool :=
  .letPrim (.length (.var (.there source)))
    (.letPrim (.lt (.var (.there .here)) (.var .here)) (.ret (.var .here)))

/-- The shared source while backend, specialized to a selected mapper. -/
def loop {Γ : List Ty} {result : Ty} (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind)) :
    Stmt signatures (.nat :: Γ) result :=
  .while (guard source) (iteration fn same source target)

/-- Fill a disjoint destination prefix. The builder introduces only a scoped
cursor and falls through normally, so a frontend may compose its continuation. -/
def into {Γ : List Ty} {result : Ty} (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind)) :
    Stmt signatures Γ result :=
  .letPrim (.atom (.nat 0)) (loop fn same source target)

/-- Allocate initialized output, fill it by actual calls, and return its fresh
handle. The second argument is the initializer required by source allocation;
every output position is subsequently overwritten with its mapped value. -/
def body (fn : Fin signatures.length)
    (same : signatures[fn] = signature inputKind outputKind) :
    Stmt signatures [.buffer inputKind, outputKind.toTy] (.buffer outputKind) :=
  .letPrim (.length (.var .here))
    (.alloc (.var .here) (.var (.there (.there .here)))
      (.seq (into fn same (.there (.there .here)) .here) (.ret (.var .here))))

private def cursorState {Γ : List Ty} (locals : Env Γ) (index : Nat) (heap : Heap) :
    State (.nat :: Γ) :=
  State.cons index ⟨locals, heap⟩

private theorem iteration_total {Γ : List Ty} {result : Ty}
    {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract program fn same f)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind))
    (output : Array (CellValue outputKind)) (index : Nat) (heap : Heap)
    (separated : (locals.get target).Disjoint (locals.get source))
    (extent : input.size ≤ output.size) (available : index < input.size)
    (observed : (locals.get source).Contents heap input)
    (initialized : (locals.get target).Contents heap (copied (input.map f) output 0 index)) :
    TotalWP program (iteration (result := result) fn same source target)
      (fun finish => ∃ finalHeap, finish = cursorState locals (index + 1) finalHeap ∧
        (locals.get source).Contents finalHeap input ∧
        (locals.get target).Contents finalHeap (copied (input.map f) output 0 (index + 1)) ∧
        (locals.get target).PreservesOutside heap finalHeap)
      (fun _ _ => False) (cursorState locals index heap) := by
  unfold iteration
  apply TotalWP.read_contents (entry := cursorState locals index heap)
    (buffer := .var (.there source)) (index := .var .here) observed available
  apply TotalWP.callOfEq same callee trivial
  intro value afterCall property
  have valueEq : value = outputKind.toValue (f input[index]) := by
    simpa [signature, Args.eval, cursorState, State.cons, Env.head, Env.get,
      Env.cons, CellTy.ofValue_toValue] using property.1
  have sourceNow := property.2 (locals.get source) input observed
  have targetNow := property.2 (locals.get target) _ initialized
  have targetBound : index < (copied (input.map f) output 0 index).size := by
    simp only [copied_size]
    omega
  obtain ⟨finalHeap, written, updated⟩ :=
    targetNow.write_exists targetBound (f input[index])
  have updatedContents : (locals.get target).Contents finalHeap
      (copied (input.map f) output 0 (index + 1)) := by
    have step := copied_step (input.map f) output 0
      (index := index) (by simpa only [Array.size_map] using available)
      (by simpa only [Array.size_map, Nat.zero_add] using extent)
    simp only [Nat.zero_add, Array.getElem_map] at step
    simpa only [step] using updated
  have calleeFrame : (locals.get target).PreservesOutside heap afterCall := by
    intro kind other values _ contents
    exact property.2 other values contents
  apply (TotalWP.seq_iff _ _).mpr
  apply TotalWP.write (heap := finalHeap)
  · change afterCall.write (locals.get target) index (outputKind.ofValue value) =
      .ok finalHeap
    rw [valueEq, CellTy.ofValue_toValue]
    exact written
  · apply TotalWP.assign
    exact ⟨finalHeap, rfl, sourceNow.write_of_disjoint written separated,
      updatedContents, calleeFrame.trans (PreservesOutside.write written)⟩

private theorem loop_total {Γ : List Ty} {result : Ty}
    {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract program fn same f)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind))
    (output : Array (CellValue outputKind))
    (separated : (locals.get target).Disjoint (locals.get source))
    (extent : input.size ≤ output.size) (index : Nat) (heap : Heap)
    (bound : index ≤ input.size) (observed : (locals.get source).Contents heap input)
    (initialized : (locals.get target).Contents heap (copied (input.map f) output 0 index)) :
    TotalWP program (loop (result := result) fn same source target)
      (fun finish => ∃ finalHeap, finish = cursorState locals input.size finalHeap ∧
        (locals.get source).Contents finalHeap input ∧
        (locals.get target).Contents finalHeap
          (copied (input.map f) output 0 input.size) ∧
        (locals.get target).PreservesOutside heap finalHeap)
      (fun _ _ => False) (cursorState locals index heap) := by
  have recurse : ∀ remaining index heap, input.size - index = remaining →
      index ≤ input.size → (locals.get source).Contents heap input →
      (locals.get target).Contents heap (copied (input.map f) output 0 index) →
      TotalWP program (loop (result := result) fn same source target)
        (fun finish => ∃ finalHeap, finish = cursorState locals input.size finalHeap ∧
          (locals.get source).Contents finalHeap input ∧
          (locals.get target).Contents finalHeap
            (copied (input.map f) output 0 input.size) ∧
          (locals.get target).PreservesOutside heap finalHeap)
        (fun _ _ => False) (cursorState locals index heap) := by
    intro remaining
    induction remaining using Nat.strong_induction_on with
    | h remaining ih =>
      intro index heap count bound observed initialized
      rw [loop, TotalWP.while_iff]
      simp only [guard, TotalWP.letPrim_iff, TotalWP.ret_iff]
      change if decide (index < (locals.get source).length) then _ else _
      by_cases active : index < input.size
      · have selected : decide (index < (locals.get source).length) = true := by
          simpa only [← observed.size_eq, decide_eq_true_eq] using active
        rw [selected]
        apply (iteration_total callee source target locals input output index heap
          separated extent active observed initialized).mono_post
        · rintro _ ⟨nextHeap, rfl, sourceKept, targetUpdated, frame⟩
          have rest := ih (input.size - (index + 1)) (by omega)
            (index + 1) nextHeap rfl (by omega) sourceKept targetUpdated
          exact rest.mono_post
            (by
              rintro _ ⟨finalHeap, rfl, sourceFinal, targetFinal, restFrame⟩
              exact ⟨finalHeap, rfl, sourceFinal, targetFinal, frame.trans restFrame⟩)
            (fun _ _ impossible => impossible)
        · exact fun _ _ impossible => impossible
      · have selected : decide (index < (locals.get source).length) = false := by
          simpa only [← observed.size_eq, decide_eq_false_iff_not] using active
        rw [selected]
        have complete : index = input.size := by omega
        subst index
        exact ⟨heap, rfl, observed, initialized, PreservesOutside.refl _ _⟩
  exact recurse _ index heap rfl bound observed initialized

/-- Generic mathematical contract for the in-place destination builder.
The input and every view disjoint from the destination retain their contents.
The source and target variables may occur anywhere in the caller environment. -/
theorem into_total {Γ : List Ty} {result : Ty}
    {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract program fn same f)
    (source : Var Γ (.buffer inputKind)) (target : Var Γ (.buffer outputKind))
    (locals : Env Γ) (input : Array (CellValue inputKind))
    (output : Array (CellValue outputKind)) (heap : Heap)
    (separated : (locals.get target).Disjoint (locals.get source))
    (extent : input.size ≤ output.size)
    (observed : (locals.get source).Contents heap input)
    (initialized : (locals.get target).Contents heap output) :
    TotalWP program (into (result := result) fn same source target)
      (fun finish => finish.locals = locals ∧
        (locals.get source).Contents finish.heap input ∧
        (locals.get target).Contents finish.heap
          (copied (input.map f) output 0 input.size) ∧
        (locals.get target).PreservesOutside heap finish.heap)
      (fun _ _ => False) ⟨locals, heap⟩ := by
  have initialFacts : (locals.get target).Contents heap (copied (input.map f) output 0 0) := by
    simpa only [copied_zero] using initialized
  rw [into, TotalWP.letPrim_iff]
  exact (loop_total callee source target locals input output separated extent 0 heap
    (Nat.zero_le _) observed initialFacts).mono_post
    (by
      rintro _ ⟨finalHeap, rfl, sourceFinal, targetFinal, frame⟩
      exact ⟨rfl, sourceFinal, targetFinal, frame⟩)
    (fun _ _ impossible => impossible)

/-- Fresh source `map` returns precisely native `Array.map` and preserves all
old heap observations. Its initializer has no effect on the returned array.
The only callback premise is a contract for the actual selected source body. -/
theorem body_total {program : Program signatures} {fn : Fin signatures.length}
    {same : signatures[fn] = signature inputKind outputKind}
    {f : CellValue inputKind → CellValue outputKind} (callee : Contract program fn same f)
    (source : Buffer inputKind) (input : Array (CellValue inputKind))
    (initial : CellValue outputKind) (heap : Heap)
    (observed : source.Contents heap input) :
    TotalWP program (body fn same) (fun _ => False)
      (fun target finish => target.Contents finish.heap (input.map f) ∧
        target.object = heap.objects.size ∧ PreservesContents heap finish.heap)
      ⟨Env.cons source (Env.cons (outputKind.toValue initial) Env.empty), heap⟩ := by
  rw [body, TotalWP.letPrim_iff]
  simp only [Prim.eval, Atom.eval, Env.cons_here]
  apply (TotalWP.alloc_iff (kind := outputKind)
    (entry := State.cons (τ := .nat) source.length
      ⟨Env.cons (τ := .buffer inputKind) source
        (Env.cons (τ := outputKind.toTy) (outputKind.toValue initial) Env.empty), heap⟩)
    (.var .here) (.var (.there (.there .here))) _).mpr
  simp only [Atom.eval, State.locals_cons, State.heap_cons,
    Env.cons_here, Env.cons_there, CellTy.ofValue_toValue]
  let allocated := heap.alloc (τ := outputKind) source.length initial
  let locals : Env [.buffer outputKind, .nat, .buffer inputKind, outputKind.toTy] :=
    Env.cons allocated.1
    (Env.cons source.length (Env.cons source
      (Env.cons (outputKind.toValue initial) Env.empty)))
  change TotalWP program
    (.seq (into fn same (.there (.there .here)) .here) (.ret (.var .here)))
    _ _ ⟨locals, allocated.2⟩
  have sourceNow : source.Contents allocated.2 input := observed.alloc _ _
  have targetNow : allocated.1.Contents allocated.2 (Array.replicate source.length initial) :=
    heap.alloc_contents _ _
  have separated : allocated.1.Disjoint source := observed.valid.rooted.disjoint_alloc _ _
  have extent : input.size ≤ (Array.replicate source.length initial).size :=
    (observed.size_eq.trans Array.size_replicate.symm).le
  apply TotalWP.seq
    ((into_total callee (.there (.there .here)) .here locals input _ allocated.2
      separated extent sourceNow targetNow).mono_post (fun _ property => property)
        (fun _ _ impossible => False.elim impossible))
  rintro finish ⟨sameLocals, _, mapped, frame⟩
  apply (TotalWP.ret_iff _).mpr
  have mappedContents : allocated.1.Contents finish.heap (input.map f) := by
    have complete := copied_replicate (input.map f) initial
    rw [Array.size_map] at complete
    simpa only [← observed.size_eq, complete] using mapped
  have oldFrame : PreservesContents heap finish.heap := by
    intro kind other values contents
    exact frame other values (contents.valid.rooted.disjoint_alloc _ _)
      (contents.alloc _ _)
  simpa only [sameLocals, Atom.eval, locals, Env.cons_here, State.heap_tail,
    allocated, Heap.alloc_object] using
    (show allocated.1.Contents finish.heap (input.map f) ∧
      allocated.1.object = heap.objects.size ∧ PreservesContents heap finish.heap from
      ⟨mappedContents, heap.alloc_object source.length initial, @oldFrame⟩)

end Buffer.Map

end Complexity.Language
