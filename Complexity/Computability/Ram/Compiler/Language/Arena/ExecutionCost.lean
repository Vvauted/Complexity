/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Costs of allocation-ready source executions

`ArenaExecutionCost` observes the same finite source `Exec` already indexed by
`ArenaReady`. It neither computes from a proof into `Nat` nor supplies source
termination. Cursor indices describe reserved storage, not an instruction budget.

The nonallocating rules retain the existing compiler-derived `ExecutionCost`
formulas, including return flags, loop guards and actual callee-frame work.
Allocation charges `14 * length + 18` for the actual operand assignments and
initialization loop, as established by `lowerAlloc_measured`. Its static code
size is not its dynamic cost; length zero still performs the fixed overhead.

Counts cover `lowerStmtCore`. Function-body flag initialization, an outer
invocation and session bootstrap retain their separate existing boundaries.
The legacy realization and cost interfaces embed without new assumptions and
without changing any count or numeric cursor.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The compiler-derived core count of the same allocation-ready execution.
Each rule observes only runtime work emitted for that executed source branch. -/
inductive ArenaExecutionCost {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit : Nat} :
    {depth next₀ next₁ : Nat} → {Γ : List Ty} → {result : Ty} →
      {stmt : Complexity.Language.Stmt signatures Γ result} →
      {entry finish : Complexity.Language.State Γ} → {control : Control result} →
      {execution : Complexity.Language.Exec program stmt entry finish control} →
      ArenaReady execution w heapLimit depth next₀ next₁ → Nat → Prop where
  | skip {Γ : List Ty} {result : Ty} {depth next : Nat}
      (entry : Complexity.Language.State Γ) :
      ArenaExecutionCost (ArenaReady.skip (program := program) (w := w)
        (heapLimit := heapLimit) (result := result) (depth := depth) (next := next) entry) 0
  | assign {Γ : List Ty} {τ result : Ty} {depth next : Nat}
      (target : Var Γ τ) (value : Prim Γ τ) (entry : Complexity.Language.State Γ)
      {fits : PrimFits w entry.locals value} :
      ArenaExecutionCost (ArenaReady.assign (program := program) (heapLimit := heapLimit)
        (result := result) (depth := depth) (next := next) target value entry fits)
        (primCodeSize value)
  | letPrim {Γ : List Ty} {τ result : Ty} {depth next₀ next₁ : Nat} {value : Prim Γ τ}
      {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
      {entry : Complexity.Language.State Γ} {finish : Complexity.Language.State (τ :: Γ)}
      {control : Control result} {fits : PrimFits w entry.locals value}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons (value.eval entry.locals) entry) finish control}
      {ready : ArenaReady body w heapLimit depth next₀ next₁} {steps : Nat}
      (tail : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.letPrim fits ready) (primCodeSize value + steps)
  | read {Γ : List Ty} {result : Ty} {kind : CellTy} {depth next₀ next₁ : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (kind.toTy :: Γ)} {control : Control result}
      {value : CellValue kind} {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {indexFits : index.eval entry.locals < 2 ^ w}
      {loaded : entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value}
      {valueFits : ValueFits w (kind.toValue value)}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) finish control}
      {ready : ArenaReady body w heapLimit depth next₀ next₁}
      {steps : Nat} (tail : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.read (loaded := loaded) bufferFits indexFits valueFits ready)
        (readCodeSize + steps)
  | write {Γ : List Ty} {result : Ty} {kind : CellTy} {depth next : Nat}
      {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat} {value : Atom Γ kind.toTy}
      {entry : Complexity.Language.State Γ} {heap : Heap}
      {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {indexFits : index.eval entry.locals < 2 ^ w}
      {valueFits : ValueFits w (value.eval entry.locals)}
      {written : entry.heap.write (buffer.eval entry.locals) (index.eval entry.locals)
        (kind.ofValue (value.eval entry.locals)) = .ok heap} :
      ArenaExecutionCost (ArenaReady.write (program := program) (heapLimit := heapLimit)
        (result := result) (depth := depth) (next := next) (written := written)
        bufferFits indexFits valueFits) writeCodeSize
  | slice {Γ : List Ty} {result : Ty} {kind : CellTy} {depth next₀ next₁ : Nat}
      {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)} {control : Control result}
      {view : Buffer kind} {bufferFits : ValueFits w (buffer.eval entry.locals)}
      {offsetFits : offset.eval entry.locals < 2 ^ w}
      {lengthFits : length.eval entry.locals < 2 ^ w}
      {sliced : (buffer.eval entry.locals).slice (offset.eval entry.locals)
        (length.eval entry.locals) = .ok view}
      {viewFits : ValueFits w (τ := .buffer kind) view}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons view entry) finish control}
      {ready : ArenaReady body w heapLimit depth next₀ next₁}
      {steps : Nat} (tail : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.slice (sliced := sliced) bufferFits offsetFits lengthFits viewFits ready)
        (sliceCodeSize + steps)
  | alloc {Γ : List Ty} {result : Ty} {kind : CellTy} {depth next₀ next₁ : Nat}
      {length : Atom Γ .nat} {initial : Atom Γ kind.toTy}
      {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {finish : Complexity.Language.State (.buffer kind :: Γ)} {control : Control result}
      {body : Complexity.Language.Exec program continuation
        (let allocated := entry.heap.alloc (τ := kind) (length.eval entry.locals)
          (kind.ofValue (initial.eval entry.locals))
         Complexity.Language.State.cons allocated.1 ⟨entry.locals, allocated.2⟩)
        finish control}
      {initialFits : ValueFits w (initial.eval entry.locals)}
      {capacity : next₀ + length.eval entry.locals ≤ heapLimit}
      {ready : ArenaReady body w heapLimit depth (next₀ + length.eval entry.locals) next₁}
      {steps : Nat} (tail : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.alloc initialFits capacity ready)
        (14 * length.eval entry.locals + 18 + steps)
  | seqNormal {Γ : List Ty} {result : Ty} {depth next₀ middleCursor next₁ : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry middle finish : Complexity.Language.State Γ} {control : Control result}
      {head : Complexity.Language.Exec program first entry middle .normal}
      {tail : Complexity.Language.Exec program second middle finish control}
      {headReady : ArenaReady head w heapLimit depth next₀ middleCursor}
      {tailReady : ArenaReady tail w heapLimit depth middleCursor next₁}
      {firstSteps secondSteps : Nat}
      (firstCost : ArenaExecutionCost headReady firstSteps)
      (secondCost : ArenaExecutionCost tailReady secondSteps) :
      ArenaExecutionCost (.seqNormal headReady tailReady) (firstSteps + 2 + secondSteps)
  | seqReturn {Γ : List Ty} {result : Ty} {depth next₀ next₁ : Nat}
      {first second : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {value : Value result}
      {head : Complexity.Language.Exec program first entry finish (.returned value)}
      {ready : ArenaReady head w heapLimit depth next₀ next₁}
      {steps : Nat} (cost : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.seqReturn (second := second) ready) (steps + 3)
  | iteTrue {Γ : List Ty} {result : Ty} {depth next₀ next₁ : Nat}
      {condition : Atom Γ .bool} {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = true}
      {body : Complexity.Language.Exec program yes entry finish control}
      {ready : ArenaReady body w heapLimit depth next₀ next₁}
      {steps : Nat} (cost : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.iteTrue (no := no) (test := test) ready) (steps + 3)
  | iteFalse {Γ : List Ty} {result : Ty} {depth next₀ next₁ : Nat}
      {condition : Atom Γ .bool} {yes no : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ} {control : Control result}
      {test : condition.eval entry.locals = false}
      {body : Complexity.Language.Exec program no entry finish control}
      {ready : ArenaReady body w heapLimit depth next₀ next₁}
      {steps : Nat} (cost : ArenaExecutionCost ready steps) :
      ArenaExecutionCost (.iteFalse (yes := yes) (test := test) ready) (steps + 2)
  | whileFalse {Γ : List Ty} {result : Ty} {depth next₀ next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry finish : Complexity.Language.State Γ}
      {test : Complexity.Language.Exec program guard entry finish (.returned false)}
      {ready : ArenaReady test w heapLimit depth next₀ next₁}
      {guardSteps : Nat} (guardCost : ArenaExecutionCost ready guardSteps) :
      ArenaExecutionCost (.whileFalse (body := body) ready) (guardSteps + 11)
  | whileTrue {Γ : List Ty} {result : Ty} {depth next₀ guardCursor bodyCursor next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard afterBody finish : Complexity.Language.State Γ} {control : Control result}
      {test : Complexity.Language.Exec program guard entry afterGuard (.returned true)}
      {iteration : Complexity.Language.Exec program body afterGuard afterBody .normal}
      {rest : Complexity.Language.Exec program (.while guard body) afterBody finish control}
      {testReady : ArenaReady test w heapLimit depth next₀ guardCursor}
      {bodyReady : ArenaReady iteration w heapLimit depth guardCursor bodyCursor}
      {restReady : ArenaReady rest w heapLimit depth bodyCursor next₁}
      {guardSteps bodySteps restSteps : Nat}
      (guardCost : ArenaExecutionCost testReady guardSteps)
      (bodyCost : ArenaExecutionCost bodyReady bodySteps)
      (restCost : ArenaExecutionCost restReady restSteps) :
      ArenaExecutionCost (.whileTrue testReady bodyReady restReady)
        (guardSteps + bodySteps + restSteps + 10)
  | whileReturn {Γ : List Ty} {result : Ty} {depth next₀ guardCursor next₁ : Nat}
      {guard : Complexity.Language.Stmt signatures Γ .bool}
      {body : Complexity.Language.Stmt signatures Γ result}
      {entry afterGuard finish : Complexity.Language.State Γ} {value : Value result}
      {test : Complexity.Language.Exec program guard entry afterGuard (.returned true)}
      {iteration : Complexity.Language.Exec program body afterGuard finish (.returned value)}
      {testReady : ArenaReady test w heapLimit depth next₀ guardCursor}
      {bodyReady : ArenaReady iteration w heapLimit depth guardCursor next₁}
      {guardSteps bodySteps : Nat}
      (guardCost : ArenaExecutionCost testReady guardSteps)
      (bodyCost : ArenaExecutionCost bodyReady bodySteps) :
      ArenaExecutionCost (.whileReturn testReady bodyReady) (guardSteps + bodySteps + 17)
  | ret {Γ : List Ty} {result : Ty} {depth next : Nat}
      (value : Atom Γ result) (entry : Complexity.Language.State Γ)
      {fits : ValueFits w (value.eval entry.locals)} :
      ArenaExecutionCost (ArenaReady.ret (program := program) (heapLimit := heapLimit)
        (depth := depth) (next := next) value entry fits) (2 * fieldCount result + 2)
  | callReturn {Γ : List Ty} {result : Ty} {depth next₀ calleeCursor next₁ : Nat}
      {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
      {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
      {entry : Complexity.Language.State Γ}
      {calleeFinish : Complexity.Language.State signatures[fn].params}
      {value : Value signatures[fn].result}
      {finish : Complexity.Language.State (signatures[fn].result :: Γ)}
      {control : Control result} {arguments : EnvFits w (args.eval entry.locals)}
      {callee : Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)}
      {body : Complexity.Language.Exec program continuation
        (Complexity.Language.State.cons value (entry.restore calleeFinish)) finish control}
      {calleeReady : ArenaReady callee w heapLimit depth next₀ calleeCursor}
      {bodyReady : ArenaReady body w heapLimit (depth + 1) calleeCursor next₁}
      {calleeSteps bodySteps : Nat}
      (calleeCost : ArenaExecutionCost calleeReady calleeSteps)
      (bodyCost : ArenaExecutionCost bodyReady bodySteps) :
      ArenaExecutionCost (.callReturn arguments calleeReady bodyReady)
        (callCost program fn (calleeSteps + 2) + bodySteps)

/-- Every allocation-ready finite execution has a cost observation without a
supplied bound. This proves existence in `Prop`, not proof-to-number computation. -/
theorem ArenaReady.exists_cost {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth next₀ next₁ : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish control}
    (ready : ArenaReady execution w heapLimit depth next₀ next₁) :
    ∃ steps, ArenaExecutionCost ready steps := by
  induction ready with
  | skip entry => exact ⟨0, .skip entry⟩
  | assign target value entry fits => exact ⟨_, .assign target value entry (fits := fits)⟩
  | letPrim fits ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .letPrim (fits := fits) cost⟩
  | @read Γ result kind w heapLimit depth next₀ next₁ buffer index continuation
      entry finish control value loaded body bufferFits indexFits valueFits ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .read (bufferFits := bufferFits) (indexFits := indexFits)
        (loaded := loaded) (valueFits := valueFits) cost⟩
  | @write Γ result kind w heapLimit depth next buffer index value entry heap
      written bufferFits indexFits valueFits =>
      exact ⟨_, .write (bufferFits := bufferFits) (indexFits := indexFits)
        (valueFits := valueFits) (written := written)⟩
  | @slice Γ result kind w heapLimit depth next₀ next₁ buffer offset length continuation
      entry finish control view sliced body bufferFits offsetFits lengthFits viewFits ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .slice (bufferFits := bufferFits) (offsetFits := offsetFits)
        (lengthFits := lengthFits) (sliced := sliced) (viewFits := viewFits) cost⟩
  | alloc initialFits capacity ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .alloc (initialFits := initialFits) (capacity := capacity) cost⟩
  | seqNormal headReady tailReady ihHead ihTail =>
      obtain ⟨firstSteps, firstCost⟩ := ihHead
      obtain ⟨secondSteps, secondCost⟩ := ihTail
      exact ⟨_, .seqNormal firstCost secondCost⟩
  | seqReturn ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .seqReturn cost⟩
  | @iteTrue Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .iteTrue (test := test) cost⟩
  | @iteFalse Γ result w heapLimit depth next₀ next₁ condition yes no entry finish control
      test body ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .iteFalse (test := test) cost⟩
  | whileFalse ready ih =>
      obtain ⟨steps, cost⟩ := ih
      exact ⟨_, .whileFalse cost⟩
  | whileTrue testReady bodyReady restReady ihTest ihBody ihRest =>
      obtain ⟨guardSteps, guardCost⟩ := ihTest
      obtain ⟨bodySteps, bodyCost⟩ := ihBody
      obtain ⟨restSteps, restCost⟩ := ihRest
      exact ⟨_, .whileTrue guardCost bodyCost restCost⟩
  | whileReturn testReady bodyReady ihTest ihBody =>
      obtain ⟨guardSteps, guardCost⟩ := ihTest
      obtain ⟨bodySteps, bodyCost⟩ := ihBody
      exact ⟨_, .whileReturn guardCost bodyCost⟩
  | ret value entry fits => exact ⟨_, .ret value entry (fits := fits)⟩
  | callReturn arguments calleeReady bodyReady ihCallee ihBody =>
      obtain ⟨calleeSteps, calleeCost⟩ := ihCallee
      obtain ⟨bodySteps, bodyCost⟩ := ihBody
      exact ⟨_, .callReturn (arguments := arguments) calleeCost bodyCost⟩

/-- Legacy execution costs retain exactly their original count after lifting
readiness. This imposes no arena representation, rootedness or capacity premise. -/
theorem ExecutionCost.arena {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w depth : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : RealizedExec program w depth stmt entry finish control}
    {steps : Nat} (cost : ExecutionCost execution steps) (heapLimit next : Nat) :
    ArenaExecutionCost (execution.arenaReady heapLimit next) steps := by
  induction cost with
  | skip entry => exact .skip entry
  | @assign Γ τ result depth target value entry fits =>
      exact .assign target value entry (fits := fits)
  | @letPrim Γ τ result depth value continuation entry finish control fits body steps _ ih =>
      exact .letPrim (fits := fits) ih
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits body steps _ ih =>
      exact .read (bufferFits := bufferFits) (indexFits := indexFits)
        (loaded := loaded) (valueFits := valueFits) ih
  | @write Γ result kind depth buffer index value entry heap
      bufferFits indexFits valueFits written =>
      exact .write (bufferFits := bufferFits) (indexFits := indexFits)
        (valueFits := valueFits) (written := written)
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits body steps _ ih =>
      exact .slice (bufferFits := bufferFits) (offsetFits := offsetFits)
        (lengthFits := lengthFits) (sliced := sliced) (viewFits := viewFits) ih
  | seqNormal _ _ ihHead ihTail => exact .seqNormal ihHead ihTail
  | seqReturn _ ih => exact .seqReturn ih
  | @iteTrue Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteTrue (test := test) ih
  | @iteFalse Γ result depth condition yes no entry finish control test body steps _ ih =>
      exact .iteFalse (test := test) ih
  | whileFalse _ ih => exact .whileFalse ih
  | whileTrue _ _ _ ihGuard ihBody ihRest => exact .whileTrue ihGuard ihBody ihRest
  | whileReturn _ _ ihGuard ihBody => exact .whileReturn ihGuard ihBody
  | @ret Γ result depth value entry fits => exact .ret value entry (fits := fits)
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments callee body calleeSteps bodySteps _ _ ihCallee ihBody =>
      exact .callReturn (arguments := arguments) ihCallee ihBody

namespace ArenaExecutionCost

private theorem observations_eq {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth next₀ next₁ w' heapLimit' depth' next₀' next₁' : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish finish' : Complexity.Language.State Γ} {control control' : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish control}
    {execution' : Complexity.Language.Exec program stmt entry finish' control'}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁}
    {ready' : ArenaReady execution' w' heapLimit' depth' next₀' next₁'}
    {steps steps' : Nat} (_ : ArenaExecutionCost ready steps)
    (_ : ArenaExecutionCost ready' steps') : finish = finish' ∧ control = control' :=
  execution.deterministic execution'

/-- The same source statement and entry state determine one core count.
Word width, heap limit, call capacity, cursor placement and readiness witnesses
do not change the observation. Independent source determinism aligns the
actual intermediate states; no machine representation or time bound is used. -/
theorem deterministic {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {w heapLimit depth next₀ next₁ : Nat}
    {Γ : List Ty} {result : Ty} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Complexity.Language.State Γ} {control : Control result}
    {execution : Complexity.Language.Exec program stmt entry finish control}
    {ready : ArenaReady execution w heapLimit depth next₀ next₁} {steps : Nat}
    (first : ArenaExecutionCost ready steps) :
    ∀ {w' heapLimit' depth' next₀' next₁' : Nat}
      {finish' : Complexity.Language.State Γ} {control' : Control result}
      {execution' : Complexity.Language.Exec program stmt entry finish' control'}
      {ready' : ArenaReady execution' w' heapLimit' depth' next₀' next₁'} {steps' : Nat},
      ArenaExecutionCost ready' steps' → steps = steps' := by
  induction first with
  | skip =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second
      rfl
  | assign =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second
      rfl
  | letPrim tail ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | letPrim tail' => rw [ih tail']
  | @read Γ result kind depth next₀ next₁ buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits body ready steps tail ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | @read _ _ _ _ _ _ _ _ _ _ _ _ value' _ _ loaded' _ _ _ _ tail' =>
          have same : value = value' := Except.ok.inj (loaded.symm.trans loaded')
          subst value'
          rw [ih tail']
  | write =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second
      rfl
  | @slice Γ result kind depth next₀ next₁ buffer offset length continuation entry finish control
      view bufferFits offsetFits lengthFits sliced viewFits body ready steps tail ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | @slice _ _ _ _ _ _ _ _ _ _ _ _ _ view' _ _ _ sliced' _ _ _ _ tail' =>
          have same : view = view' := Except.ok.inj (sliced.symm.trans sliced')
          subst view'
          rw [ih tail']
  | alloc tail ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | alloc tail' => rw [ih tail']
  | seqNormal firstCost secondCost ihFirst ihSecond =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | seqNormal firstCost' secondCost' =>
          obtain ⟨rfl, _⟩ := observations_eq firstCost firstCost'
          rw [ihFirst firstCost', ihSecond secondCost']
      | seqReturn cost' => cases (observations_eq firstCost cost').2
  | seqReturn cost ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | seqNormal firstCost' secondCost' => cases (observations_eq cost firstCost').2
      | seqReturn cost' => rw [ih cost']
  | iteTrue cost ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | iteTrue cost' => rw [ih cost']
      | iteFalse cost' => simp_all
  | iteFalse cost ih =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | iteTrue cost' => simp_all
      | iteFalse cost' => rw [ih cost']
  | whileFalse guardCost ihGuard =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | whileFalse guardCost' => rw [ihGuard guardCost']
      | whileTrue guardCost' bodyCost' restCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileReturn guardCost' bodyCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
  | whileTrue guardCost bodyCost restCost ihGuard ihBody ihRest =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | whileFalse guardCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileTrue guardCost' bodyCost' restCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          obtain ⟨rfl, _⟩ := observations_eq bodyCost bodyCost'
          rw [ihGuard guardCost', ihBody bodyCost', ihRest restCost']
      | whileReturn guardCost' bodyCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          cases (observations_eq bodyCost bodyCost').2
  | whileReturn guardCost bodyCost ihGuard ihBody =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | whileFalse guardCost' =>
          cases Control.returned.inj (observations_eq guardCost guardCost').2
      | whileTrue guardCost' bodyCost' restCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          cases (observations_eq bodyCost bodyCost').2
      | whileReturn guardCost' bodyCost' =>
          obtain ⟨rfl, _⟩ := observations_eq guardCost guardCost'
          rw [ihGuard guardCost', ihBody bodyCost']
  | ret =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second
      rfl
  | callReturn calleeCost bodyCost ihCallee ihBody =>
      intro w' heapLimit' depth' next₀' next₁' finish' control' execution' ready' steps' second
      cases second with
      | callReturn calleeCost' bodyCost' =>
          obtain ⟨rfl, sameControl⟩ := observations_eq calleeCost calleeCost'
          cases Control.returned.inj sameControl
          rw [ihCallee calleeCost', ihBody bodyCost']

end ArenaExecutionCost

end Ram.LanguageCompiler
