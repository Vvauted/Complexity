/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap
import Complexity.Computability.Ram.Compiler.Language.Realization
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost.Depth
import Complexity.Computability.Ram.Compiler.Language.DepthBound
import Complexity.Language.Heap.Frame

/-!
# Realizing finite executions of range-preserving source programs

A source correctness proof already establishes successful heap accesses and
finite execution. For programs that only copy and compare fitting words, the
remaining value-range proof is structural: reads obtain fitting cells, writes
store fitting values, and calls preserve the same invariant on the shared heap.

`RangePreserving` checks that restricted fragment syntactically. It supports
copies, comparisons, lengths, reads, writes, branches, sequencing and calls.
Arithmetic, slicing, allocation, scratch scopes and loops are deliberately not
covered by this interface; their existing realization rules remain available.
In particular, this predicate does not establish index validity or termination.

`RealizedExec.exists_of_exec` lifts an independently successful finite source
execution without proving its algorithm again or choosing a runtime budget.
Its existential depth is sufficient call nesting, not elapsed time. Heap value
ranges are exactly those already required by the compiler's `HeapRep`.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Every cell in the current source heap has an exact word-sized scalar value.
This is the range field of `HeapRep`, without a target memory or placement. -/
def HeapFits (w : Nat) (heap : Heap) : Prop :=
  ∀ {τ : CellTy} {object : Nat} {values : Array (CellValue τ)},
    heap.object? τ object = some values →
      ∀ (index : Nat) (bound : index < values.size), cellToNat values[index] < 2 ^ w

/-- The existing RAM representation already supplies all source heap ranges. -/
theorem HeapRep.heapFits {w heapLimit : Nat} {placement : Nat → Word w}
    {heap : Heap} {target : Source.State w}
    (represented : HeapRep placement heapLimit heap target) : HeapFits w heap :=
  represented.ranges

namespace HeapFits

/-- A successful source read returns a fitting value from the current heap. -/
theorem read {w : Nat} {heap : Heap} (fits : HeapFits w heap)
    {τ : CellTy} {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    (loaded : heap.read buffer index = .ok value) : cellToNat value < 2 ^ w := by
  obtain ⟨values, found, extent, bound, same⟩ := Heap.read_eq_ok_iff.mp loaded
  have cellFits := fits found (buffer.offset + index) (by omega)
  simpa only [same] using cellFits

/-- Writing a fitting scalar preserves all current cell ranges, including
overlapping views. No old heap snapshot or disjoint-buffer premise is used. -/
theorem write {w : Nat} {heap finish : Heap} (fits : HeapFits w heap)
    {τ : CellTy} {buffer : Buffer τ} {index : Nat} {value : CellValue τ}
    (written : heap.write buffer index value = .ok finish)
    (valueFits : cellToNat value < 2 ^ w) : HeapFits w finish := by
  obtain ⟨values, found, extent, bound, rfl⟩ := Heap.write_eq_ok_iff.mp written
  intro σ other otherValues otherFound next nextBound
  by_cases sameObject : buffer.object = other
  · subst other
    have updatedFound :
        (heap.replace buffer.object
          (values.setIfInBounds (buffer.offset + index) value)).object? τ buffer.object =
            some (values.setIfInBounds (buffer.offset + index) value) :=
      Heap.object?_replace_self (Heap.object_lt_size found)
    have sameStored : (⟨σ, otherValues⟩ : HeapObject) =
        ⟨τ, values.setIfInBounds (buffer.offset + index) value⟩ := by
      apply Option.some.inj
      exact (Heap.object?_eq_some_iff.mp otherFound).symm.trans
        (Heap.object?_eq_some_iff.mp updatedFound)
    have sameType : σ = τ := congrArg Sigma.fst sameStored
    subst σ
    have sameValues : otherValues = values.setIfInBounds (buffer.offset + index) value :=
      Option.some.inj (otherFound.symm.trans updatedFound)
    subst otherValues
    have originalBound : next < values.size := by
      simpa only [Array.size_setIfInBounds] using nextBound
    by_cases sameCell : buffer.offset + index = next
    · subst next
      simpa only [Array.getElem_setIfInBounds_self] using valueFits
    · simpa only [Array.getElem_setIfInBounds_ne originalBound sameCell] using
        fits found next originalBound
  · have originalFound : heap.object? σ other = some otherValues :=
      (Heap.object?_replace_ne sameObject).symm.trans otherFound
    exact fits originalFound next nextBound

end HeapFits

/-- Variables inherit their current range; literal values must fit explicitly. -/
def AtomBounded (w : Nat) {Γ : List Ty} : {τ : Ty} → Atom Γ τ → Prop
  | _, .var _ => True
  | _, .nat value => value < 2 ^ w
  | _, .bool value => (if value then 1 else 0) < 2 ^ w
  | _, .unit => True

/-- Copies, comparisons and lengths do not create a larger scalar value.
Arithmetic primitives use their separate, input-dependent realization rules. -/
def PrimBounded (w : Nat) {Γ : List Ty} : {τ : Ty} → Prim Γ τ → Prop
  | _, .atom atom => AtomBounded w atom
  | _, .eq left right | _, .lt left right | _, .le left right =>
      AtomBounded w left ∧ AtomBounded w right
  | _, .length buffer => AtomBounded w buffer
  | _, .add _ _ | _, .mul _ _ | _, .sub _ _ | _, .div _ _ | _, .mod _ _ => False

/-- All actual call operands are drawn from fitting locals or fitting literals. -/
def ArgsBounded (w : Nat) {Γ : List Ty} : {params : List Ty} → Args Γ params → Prop
  | _, .nil => True
  | _, .cons value rest => AtomBounded w value ∧ ArgsBounded w rest

/-- The finite range-preserving fragment. Call bodies are checked separately
for every function in the same program, so recursive calls need no unfolding. -/
def RangePreserving (w : Nat) {signatures : List Signature} :
    {Γ : List Ty} → {result : Ty} → Complexity.Language.Stmt signatures Γ result → Prop
  | _, _, .skip => True
  | _, _, .assign _ value => PrimBounded w value
  | _, _, .letPrim value body => PrimBounded w value ∧ RangePreserving w body
  | _, _, .read buffer index body =>
      AtomBounded w buffer ∧ AtomBounded w index ∧ RangePreserving w body
  | _, _, .write buffer index value =>
      AtomBounded w buffer ∧ AtomBounded w index ∧ AtomBounded w value
  | _, _, .seq first second => RangePreserving w first ∧ RangePreserving w second
  | _, _, .ite condition yes no =>
      AtomBounded w condition ∧ RangePreserving w yes ∧ RangePreserving w no
  | _, _, .ret value => AtomBounded w value
  | _, _, .call _ args body => ArgsBounded w args ∧ RangePreserving w body
  | _, _, .slice _ _ _ _ | _, _, .alloc _ _ _ | _, _, .scope _ | _, _, .while _ _ => False

/-- A bounded atom observes a fitting value in any fitting local environment. -/
theorem AtomBounded.fits {w : Nat} {Γ : List Ty} {τ : Ty} {atom : Atom Γ τ}
    (bounded : AtomBounded w atom) {env : Env Γ} (fits : EnvFits w env) :
    ValueFits w (atom.eval env) := by
  cases atom with
  | var v => exact fits v
  | nat value => exact bounded
  | bool value => exact bounded
  | unit => trivial

/-- The restricted primitives meet both their operand conditions and the range
of their actual mathematical result. Positive width includes Boolean true. -/
theorem PrimBounded.fits {w : Nat} (hw : 0 < w) {Γ : List Ty} {τ : Ty}
    {prim : Prim Γ τ} (bounded : PrimBounded w prim) {env : Env Γ}
    (fits : EnvFits w env) : PrimFits w env prim ∧ ValueFits w (prim.eval env) := by
  have booleanFits : ∀ value : Bool, ValueFits w (τ := .bool) value := by
    intro value
    cases value
    · exact Nat.two_pow_pos w
    · exact Nat.one_lt_two_pow (Nat.ne_of_gt hw)
  cases prim with
  | atom atom => exact ⟨AtomBounded.fits bounded fits, AtomBounded.fits bounded fits⟩
  | eq left right =>
      exact ⟨⟨bounded.1.fits fits, bounded.2.fits fits⟩, booleanFits _⟩
  | lt left right =>
      exact ⟨⟨bounded.1.fits fits, bounded.2.fits fits⟩, booleanFits _⟩
  | le left right =>
      exact ⟨⟨bounded.1.fits fits, bounded.2.fits fits⟩, booleanFits _⟩
  | length buffer => exact ⟨AtomBounded.fits bounded fits, AtomBounded.fits bounded fits⟩
  | add _ _ | mul _ _ | sub _ _ | div _ _ | mod _ _ => exact False.elim bounded

/-- A call binds the actual fitting values in parameter order. -/
theorem ArgsBounded.fits {w : Nat} {Γ params : List Ty} {args : Args Γ params}
    (bounded : ArgsBounded w args) {env : Env Γ} (fits : EnvFits w env) :
    EnvFits w (args.eval env) := by
  induction args with
  | nil => exact EnvFits.empty w
  | cons value rest ih => exact EnvFits.cons (ih bounded.2) _ (bounded.1.fits fits)

namespace RealizedExec

/-- A successful finite source execution of the restricted fragment admits
some finite call capacity and preserves all scalar ranges. The source proof
supplies every successful access and recursive termination; no time or stack
budget is assumed, and no functional property of the program is reproved. -/
theorem exists_of_exec {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w : Nat} (hw : 0 < w)
    (bodies : ∀ fn, RangePreserving w (program.body fn))
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    (execution : Complexity.Language.Exec program stmt entry finish control) :
    RangePreserving w stmt → control.Satisfies (fun _ => True) (fun _ _ => True) finish →
      EnvFits w entry.locals → HeapFits w entry.heap →
      ∃ depth, RealizedExec program w depth stmt entry finish control ∧
        EnvFits w finish.locals ∧ HeapFits w finish.heap := by
  induction execution <;> intro fragment success locals heap
  all_goals first | exact False.elim fragment | exact False.elim success | skip
  case skip state => exact ⟨0, .skip state, locals, heap⟩
  case assign target value state =>
    obtain ⟨operands, resultFits⟩ := PrimBounded.fits hw fragment locals
    exact ⟨0, .assign target value state operands, locals.set target _ resultFits, heap⟩
  case letPrim value body ih =>
    obtain ⟨operands, resultFits⟩ := PrimBounded.fits hw fragment.1 locals
    obtain ⟨depth, realized, finalLocals, finalHeap⟩ :=
      ih fragment.2 success (locals.cons _ resultFits) heap
    exact ⟨depth, .letPrim operands realized, finalLocals.tail, finalHeap⟩
  case read kind buffer index continuation entry finish control value loaded body ih =>
    have valueFits : ValueFits w (kind.toValue value) := by
      have scalarFits := heap.read loaded
      cases kind <;> exact scalarFits
    obtain ⟨depth, realized, finalLocals, finalHeap⟩ :=
      ih fragment.2.2 success (locals.cons _ valueFits) heap
    exact ⟨depth, .read (fragment.1.fits locals) (fragment.2.1.fits locals)
      loaded valueFits realized, finalLocals.tail, finalHeap⟩
  case write kind buffer index value entry finalHeap written =>
    have valueFits := fragment.2.2.fits locals
    have scalarFits : cellToNat (kind.ofValue (value.eval entry.locals)) < 2 ^ w := by
      cases kind <;> exact valueFits
    exact ⟨0, .write (fragment.1.fits locals) (fragment.2.1.fits locals) valueFits written,
      locals, heap.write written scalarFits⟩
  case seqNormal head tail ihHead ihTail =>
    obtain ⟨firstDepth, first, middleLocals, middleHeap⟩ :=
      ihHead fragment.1 trivial locals heap
    obtain ⟨secondDepth, second, finalLocals, finalHeap⟩ :=
      ihTail fragment.2 success middleLocals middleHeap
    exact ⟨max firstDepth secondDepth,
      .seqNormal (first.mono_depth (Nat.le_max_left _ _))
        (second.mono_depth (Nat.le_max_right _ _)), finalLocals, finalHeap⟩
  case seqReturn head ih =>
    obtain ⟨depth, realized, finalLocals, finalHeap⟩ := ih fragment.1 trivial locals heap
    exact ⟨depth, .seqReturn realized, finalLocals, finalHeap⟩
  case iteTrue test body ih =>
    obtain ⟨depth, realized, finalLocals, finalHeap⟩ := ih fragment.2.1 success locals heap
    exact ⟨depth, .iteTrue test realized, finalLocals, finalHeap⟩
  case iteFalse test body ih =>
    obtain ⟨depth, realized, finalLocals, finalHeap⟩ := ih fragment.2.2 success locals heap
    exact ⟨depth, .iteFalse test realized, finalLocals, finalHeap⟩
  case ret value state => exact ⟨0, .ret value state (fragment.fits locals), locals, heap⟩
  case callReturn fn args continuation entry calleeFinish value finish control callee body
      ihCallee ihBody =>
    have arguments : EnvFits w (args.eval entry.locals) := fragment.1.fits locals
    obtain ⟨calleeDepth, call, calleeLocals, calleeHeap⟩ :=
      ihCallee (bodies fn) trivial arguments heap
    obtain ⟨bodyDepth, rest, finalLocals, finalHeap⟩ :=
      ihBody fragment.2 success (locals.cons _ call.returned_fits) calleeHeap
    exact ⟨max calleeDepth bodyDepth + 1,
      .callReturn arguments (call.mono_depth (Nat.le_max_left _ _))
        (rest.mono_depth (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _))),
      finalLocals.tail, finalHeap⟩

end RealizedExec

/-- Independent source total correctness and an established instruction bound
give a conservative explicit call capacity for a range-preserving program.
The input range conditions belong only to realization; the source contract
continues to establish correctness and termination without a resource budget.
The postcondition and the cost concern the same finite source execution. -/
theorem FunctionRealizable.of_rangePreserving {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {fn : Fin signatures.length}
    {pre costPre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {bound : Env signatures[fn].params → Heap → Nat}
    (hw : 0 < w) (bodies : ∀ fn, RangePreserving w (program.body fn))
    (specification : FunctionTotal program fn pre post)
    (timeBound : FunctionCostBound program fn costPre bound)
    (capacity : ∀ args heap, pre args heap → costPre args heap → bound args heap ≤ depth) :
    FunctionRealizable program w depth fn
      (fun args heap => pre args heap ∧ costPre args heap ∧
        EnvFits w args ∧ HeapFits w heap) := by
  intro args heap ⟨input, priced, locals, cells⟩
  obtain ⟨finish, value, execution, _⟩ := specification args heap input
  obtain ⟨actualDepth, realized, _, _⟩ :=
    RealizedExec.exists_of_exec hw bodies execution (bodies fn) trivial locals cells
  obtain ⟨steps, cost⟩ := realized.exists_cost
  have instructionBound := timeBound args heap priced realized cost
  have nestingBound := capacity args heap input priced
  exact ⟨finish, value, cost.realized_at_steps.mono_depth (by omega)⟩

/-- Source total correctness and an independent nesting bound give a finite-word
realization without using instruction count as a call-stack allowance. The depth
certificate changes only the capacity of the same source execution; correctness,
heap access safety and word ranges still come from the existing contracts. -/
theorem FunctionRealizable.of_rangePreserving_depth {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {fn : Fin signatures.length}
    {pre depthPre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {bound : Env signatures[fn].params → Heap → Nat}
    (hw : 0 < w) (bodies : ∀ fn, RangePreserving w (program.body fn))
    (specification : FunctionTotal program fn pre post)
    (nesting : FunctionDepthBound program fn depthPre bound)
    (capacity : ∀ args heap, pre args heap → depthPre args heap → bound args heap ≤ depth) :
    FunctionRealizable program w depth fn
      (fun args heap => pre args heap ∧ depthPre args heap ∧
        EnvFits w args ∧ HeapFits w heap) := by
  intro args heap ⟨input, bounded, locals, cells⟩
  obtain ⟨finish, value, execution, _⟩ := specification args heap input
  obtain ⟨actualDepth, realized, _, _⟩ :=
    RealizedExec.exists_of_exec hw bodies execution (bodies fn) trivial locals cells
  exact ⟨finish, value,
    (nesting args heap bounded realized).mono_depth (capacity args heap input bounded)⟩

end Ram.LanguageCompiler
