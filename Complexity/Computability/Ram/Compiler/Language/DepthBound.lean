/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Realization

/-!
# Source bounds on simultaneous call nesting

`StmtDepthBound` reconstructs the same realized source execution at a sufficient
call capacity. Sequential statements and a call's continuation reuse capacity;
only entering a callee adds a nesting level. These rules retain the original
word ranges, source states and outcome. They neither supply termination nor
define another execution or resource interpreter.

`FunctionDepthBound` is conditional on a successful returning execution. Unlike
an instruction bound, it adds no charge for return-flag initialization: those
instructions introduce no call frame. The runner accounts separately for its
outer invocation frame.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A sufficient call capacity for every realized execution from the given
source state, preserving its word width, final state and control outcome. -/
def StmtDepthBound {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Complexity.Language.Program signatures)
    (stmt : Complexity.Language.Stmt signatures Γ result)
    (entry : Complexity.Language.State Γ) (bound : Nat) : Prop :=
  ∀ {w depth finish control},
    RealizedExec program w depth stmt entry finish control →
      RealizedExec program w bound stmt entry finish control

/-- A source-level bound on internal call nesting for a successfully returning
function. Neither a time bound nor a proof of termination is required here. -/
def FunctionDepthBound {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (pre : Env signatures[fn].params → Heap → Prop)
    (bound : Env signatures[fn].params → Heap → Nat) : Prop :=
  ∀ args heap, pre args heap → ∀ {w depth finish value},
    RealizedExec program w depth (program.body fn) ⟨args, heap⟩ finish (.returned value) →
      RealizedExec program w (bound args heap) (program.body fn)
        ⟨args, heap⟩ finish (.returned value)

namespace StmtDepthBound

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Complexity.Language.Program signatures}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry : Complexity.Language.State Γ} {bound bound' : Nat}

/-- A larger capacity still realizes the same computation. -/
theorem mono (h : StmtDepthBound program stmt entry bound) (capacity : bound ≤ bound') :
    StmtDepthBound program stmt entry bound' := by
  intro w depth finish control execution
  exact (h execution).mono_depth capacity

/-- An empty statement requires no internal call frame. -/
theorem skip (entry : Complexity.Language.State Γ) :
    StmtDepthBound program (.skip : Complexity.Language.Stmt signatures Γ result) entry 0 := by
  intro w depth finish control execution
  cases execution
  exact .skip entry

/-- Scalar and descriptor assignments introduce no call nesting. -/
theorem assign {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ)
    (entry : Complexity.Language.State Γ) :
    StmtDepthBound program (.assign target value : Complexity.Language.Stmt signatures Γ result)
      entry 0 := by
  intro w depth finish control execution
  cases execution with
  | assign target value entry fits => exact .assign target value entry fits

/-- Returning the actual value introduces no internal call frame. -/
theorem ret (value : Atom Γ result) (entry : Complexity.Language.State Γ) :
    StmtDepthBound program (.ret value) entry 0 := by
  intro w depth finish control execution
  cases execution with
  | ret value entry fits => exact .ret value entry fits

/-- A primitive binding retains the continuation's capacity at its actual value. -/
theorem letPrim {τ : Ty} (value : Prim Γ τ)
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (body : StmtDepthBound program continuation
      (Complexity.Language.State.cons (value.eval entry.locals) entry) bound) :
    StmtDepthBound program (.letPrim value continuation) entry bound := by
  intro w depth finish control execution
  cases execution with
  | letPrim fits tail => exact .letPrim fits (body tail)

/-- A successful read exposes its actual value and read equation to the
continuation's capacity argument. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    {nextBound : CellValue kind → Nat}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtDepthBound program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) (nextBound value))
    (combine : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      nextBound value ≤ bound) :
    StmtDepthBound program (.read buffer index continuation) entry bound := by
  intro w depth finish control execution
  cases execution with
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits tail =>
      exact .read bufferFits indexFits loaded valueFits
        ((body value loaded tail).mono_depth (combine value loaded))

/-- A uniform depth bound may still use the successful read equation. -/
theorem read_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtDepthBound program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtDepthBound program (.read buffer index continuation) entry bound :=
  read (nextBound := fun _ => bound) body (fun _ _ => Nat.le_refl _)

/-- A read with a value-independent continuation bound needs no read contract. -/
theorem read_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value, StmtDepthBound program continuation
      (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtDepthBound program (.read buffer index continuation) entry bound :=
  read_of_success (fun value _ => body value)

/-- An actual store has no internal call nesting; its changed heap is retained. -/
theorem write {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) (entry : Complexity.Language.State Γ) :
    StmtDepthBound program (.write buffer index value : Complexity.Language.Stmt signatures Γ result)
      entry 0 := by
  intro w depth finish control execution
  cases execution with
  | write bufferFits indexFits valueFits written =>
      exact .write bufferFits indexFits valueFits written

/-- Forming a slice leaves call capacity to the continuation at the actual view. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {nextBound : Buffer kind → Nat}
    (body : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view →
      StmtDepthBound program continuation
        (Complexity.Language.State.cons view entry) (nextBound view))
    (combine : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view → nextBound view ≤ bound) :
    StmtDepthBound program (.slice buffer offset length continuation) entry bound := by
  intro w depth finish control execution
  cases execution with
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits tail =>
      exact .slice bufferFits offsetFits lengthFits sliced viewFits
        ((body view sliced tail).mono_depth (combine view sliced))

/-- A uniform slice continuation introduces no extra call nesting. -/
theorem slice_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    (body : ∀ view, StmtDepthBound program continuation
      (Complexity.Language.State.cons view entry) bound) :
    StmtDepthBound program (.slice buffer offset length continuation) entry bound :=
  slice (nextBound := fun _ => bound) (fun view _ => body view) (fun _ _ => Nat.le_refl _)

/-- Only the selected branch contributes to call nesting. -/
theorem ite {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesDepth : condition.eval entry.locals = true → StmtDepthBound program yes entry yesBound)
    (noDepth : condition.eval entry.locals = false → StmtDepthBound program no entry noBound) :
    StmtDepthBound program (.ite condition yes no) entry
      (if condition.eval entry.locals then yesBound else noBound) := by
  intro w depth finish control execution
  cases execution with
  | iteTrue test body =>
      simpa only [test, ↓reduceIte] using RealizedExec.iteTrue test (yesDepth test body)
  | iteFalse test body =>
      simpa only [test, Bool.false_eq_true, ↓reduceIte] using
        RealizedExec.iteFalse test (noDepth test body)

/-- A true guard requires capacity only for its selected branch. -/
theorem ite_true {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    (test : condition.eval entry.locals = true)
    (body : StmtDepthBound program yes entry bound) :
    StmtDepthBound program (.ite condition yes no) entry bound := by
  intro w depth finish control execution
  cases execution with
  | iteTrue actual branch => exact .iteTrue actual (body branch)
  | iteFalse actual branch => cases test.symm.trans actual

/-- A false guard requires capacity only for its selected branch. -/
theorem ite_false {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    (test : condition.eval entry.locals = false)
    (body : StmtDepthBound program no entry bound) :
    StmtDepthBound program (.ite condition yes no) entry bound := by
  intro w depth finish control execution
  cases execution with
  | iteTrue actual branch => cases test.symm.trans actual
  | iteFalse actual branch => exact .iteFalse actual (body branch)

/-- A branch-independent capacity is the maximum, not the sum, of its branches. -/
theorem ite_max {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesDepth : StmtDepthBound program yes entry yesBound)
    (noDepth : StmtDepthBound program no entry noBound) :
    StmtDepthBound program (.ite condition yes no) entry (max yesBound noBound) := by
  intro w depth finish control execution
  cases execution with
  | iteTrue test body =>
      exact .iteTrue test ((yesDepth body).mono_depth (Nat.le_max_left _ _))
  | iteFalse test body =>
      exact .iteFalse test ((noDepth body).mono_depth (Nat.le_max_right _ _))

/-- Option matching retains its actual payload and all source effects. Neither
testing the tag nor binding its fields introduces a call frame. -/
theorem matchOption {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (noneDepth : value.eval entry.locals = none →
      StmtDepthBound program noneBranch entry bound)
    (someDepth : ∀ payload, value.eval entry.locals = some payload →
      StmtDepthBound program someBranch (Complexity.Language.State.cons payload entry) bound) :
    StmtDepthBound program (.matchOption value noneBranch someBranch) entry bound := by
  intro w depth finish control execution
  cases execution with
  | matchNone selected branch => exact .matchNone selected (noneDepth selected branch)
  | matchSome selected fits branch => exact .matchSome selected fits (someDepth _ selected branch)

/-- A known absent value needs only its selected branch's call capacity. -/
theorem match_none {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = none)
    (body : StmtDepthBound program noneBranch entry bound) :
    StmtDepthBound program (.matchOption value noneBranch someBranch) entry bound := by
  apply matchOption (fun _ => body)
  intro payload impossible
  cases selected.symm.trans impossible

/-- A present value binds its actual payload without adding a frame. -/
theorem match_some {τ : Ty} {value : Atom Γ (.option τ)} {payload : Value τ}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = some payload)
    (body : StmtDepthBound program someBranch
      (Complexity.Language.State.cons payload entry) bound) :
    StmtDepthBound program (.matchOption value noneBranch someBranch) entry bound := by
  apply matchOption
  · intro impossible
    cases selected.symm.trans impossible
  · intro actual same
    cases Option.some.inj (selected.symm.trans same)
    exact body

/-- Disjoint match branches reuse the larger call capacity, retaining the
selection equation for proofs about the actual payload. -/
theorem match_max {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {noneBound someBound : Nat}
    (noneDepth : value.eval entry.locals = none →
      StmtDepthBound program noneBranch entry noneBound)
    (someDepth : ∀ payload, value.eval entry.locals = some payload →
      StmtDepthBound program someBranch (Complexity.Language.State.cons payload entry) someBound) :
    StmtDepthBound program (.matchOption value noneBranch someBranch) entry
      (max noneBound someBound) :=
  matchOption (fun selected => StmtDepthBound.mono (noneDepth selected) (Nat.le_max_left _ _))
    (fun payload selected => StmtDepthBound.mono (someDepth payload selected)
      (Nat.le_max_right _ _))

/-- Compose through the first statement's actual normal post-state. Early
return skips the second statement, and sequential frames are reused. -/
theorem seq_of_post {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound : Nat} {post : Complexity.Language.State Γ → Prop}
    {nextBound : Complexity.Language.State Γ → Nat}
    (head : StmtDepthBound program first entry firstBound)
    (finished : ∀ {middle},
      Complexity.Language.Exec program first entry middle .normal → post middle)
    (tail : ∀ middle, post middle → StmtDepthBound program second middle (nextBound middle))
    (combine : ∀ middle, post middle → max firstBound (nextBound middle) ≤ bound)
    (earlyReturn : firstBound ≤ bound) :
    StmtDepthBound program (.seq first second) entry bound := by
  intro w depth finish control execution
  cases execution with
  | seqNormal firstExec secondExec =>
      have property := finished firstExec.erase
      have capacity := combine _ property
      exact .seqNormal ((head firstExec).mono_depth
        ((Nat.le_max_left _ _).trans capacity))
        ((tail _ property secondExec).mono_depth ((Nat.le_max_right _ _).trans capacity))
  | seqReturn firstExec => exact .seqReturn ((head firstExec).mono_depth earlyReturn)

/-- Sequential statements reuse a capacity sufficient for either statement. -/
theorem seq {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound secondBound : Nat}
    (head : StmtDepthBound program first entry firstBound)
    (tail : ∀ middle, StmtDepthBound program second middle secondBound) :
    StmtDepthBound program (.seq first second) entry (max firstBound secondBound) :=
  seq_of_post (post := fun _ => True) (nextBound := fun _ => secondBound)
    head (fun _ => trivial) (fun middle _ => tail middle)
    (fun _ _ => Nat.le_refl _) (Nat.le_max_left _ _)

/-- A callee adds one simultaneous frame; after returning, its capacity is
reused by the continuation at the actual returned value and final heap. -/
theorem call {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {pre : Env signatures[fn].params → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat}
    {post : Value signatures[fn].result → Heap → Prop}
    {nextBound : Value signatures[fn].result → Heap → Nat}
    (callee : FunctionDepthBound program fn pre calleeBound)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (returned : ∀ {finish value},
      Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) finish (.returned value) → post value finish.heap)
    (body : ∀ value heap, post value heap →
      StmtDepthBound program continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post value heap →
      max (calleeBound (args.eval entry.locals) entry.heap + 1) (nextBound value heap) ≤ bound) :
    StmtDepthBound program (.call fn args continuation) entry bound := by
  intro w depth finish control execution
  cases execution with
  | callReturn arguments calleeExec bodyExec =>
      have property := returned calleeExec.erase
      have capacity := combine _ _ property
      have calleeRebuilt := callee _ _ hpre calleeExec
      have bodyRebuilt := body _ _ property bodyExec
      cases bound with
      | zero => omega
      | succ bound =>
          exact .callReturn arguments (calleeRebuilt.mono_depth (by omega))
            (bodyRebuilt.mono_depth (by omega))

/-- A uniform continuation bound needs no independent callee result contract. -/
theorem call_uniform {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {pre : Env signatures[fn].params → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat} {nextBound : Nat}
    (callee : FunctionDepthBound program fn pre calleeBound)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, StmtDepthBound program continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtDepthBound program (.call fn args continuation) entry
      (max (calleeBound (args.eval entry.locals) entry.heap + 1) nextBound) :=
  call (post := fun _ _ => True) (nextBound := fun _ _ => nextBound) callee hpre
    (fun _ => trivial) (fun value heap _ => body value heap) (fun _ _ _ => Nat.le_refl _)

/-- Reuse a mathematical callee contract to bound its actual continuation. -/
theorem call_of_spec {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {depthPre pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat} {nextBound : Nat}
    (callee : FunctionDepthBound program fn depthPre calleeBound)
    (specification : FunctionTotal program fn pre post)
    (depthInput : depthPre (args.eval entry.locals) entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtDepthBound program continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtDepthBound program (.call fn args continuation) entry
      (max (calleeBound (args.eval entry.locals) entry.heap + 1) nextBound) := by
  apply call (post := post (args.eval entry.locals) entry.heap)
    (nextBound := fun _ _ => nextBound) callee depthInput
  · intro finish value execution
    exact specification.postcondition input execution
  · exact body
  · intro value heap property
    exact Nat.le_refl _

end StmtDepthBound

namespace FunctionDepthBound

variable {signatures : List Signature} {program : Complexity.Language.Program signatures}
variable {fn : Fin signatures.length} {pre : Env signatures[fn].params → Heap → Prop}
variable {bound bound' : Env signatures[fn].params → Heap → Nat}

/-- Enlarge a function's allowed nesting while preserving its source domain. -/
theorem mono_bound (h : FunctionDepthBound program fn pre bound)
    (capacity : ∀ args heap, pre args heap → bound args heap ≤ bound' args heap) :
    FunctionDepthBound program fn pre bound' := by
  intro args heap input w depth finish value execution
  exact (h args heap input execution).mono_depth (capacity args heap input)

/-- A statement nesting bound is already the complete function's internal
nesting bound; return-flag initialization introduces no call frame. -/
theorem of_stmt
    (body : ∀ args heap, pre args heap →
      StmtDepthBound program (program.body fn) ⟨args, heap⟩ (bound args heap)) :
    FunctionDepthBound program fn pre bound := by
  intro args heap input w depth finish value execution
  exact body args heap input execution

/-- Infer an intermediate body capacity and compare it to the proposed bound,
without asking the author to supply a second bound function for every scope. -/
theorem of_pointwise
    (body : ∀ args heap, pre args heap → ∃ capacity,
      StmtDepthBound program (program.body fn) ⟨args, heap⟩ capacity ∧
        capacity ≤ bound args heap) :
    FunctionDepthBound program fn pre bound := by
  intro args heap input w depth finish value execution
  obtain ⟨capacity, bounded, sufficient⟩ := body args heap input
  exact (bounded execution).mono_depth sufficient

end FunctionDepthBound

end Ram.LanguageCompiler
