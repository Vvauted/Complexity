/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.ExecutionCost

/-!
# Structured bounds on source execution costs

`StmtCostBound` bounds the existing compiler-derived `ExecutionCost` observation
at an actual source state. It does not define another execution or cost
interpreter, and it supplies neither correctness nor termination. Bounds are
uniform over word widths and call capacities whenever execution is realizable.

The composition rules keep primitive values, branch conditions and actual callee
returns in the source language. Callee bounds already include the callee's body
wrapper; `FunctionCostBound.of_stmt` adds the enclosing function's wrapper once.
Proposed bounds never enter the program or assign prices to its instructions.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- A conditional upper bound on every realized execution of a source statement
from the given entry. Normal continuation and early return are both covered. -/
def StmtCostBound {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (program : Complexity.Language.Program signatures)
    (stmt : Complexity.Language.Stmt signatures Γ result)
    (entry : Complexity.Language.State Γ) (bound : Nat) : Prop :=
  ∀ {w depth finish control}
    (execution : RealizedExec program w depth stmt entry finish control)
    {steps}, ExecutionCost execution steps → steps ≤ bound

namespace StmtCostBound

variable {signatures : List Signature} {Γ : List Ty} {result : Ty}
variable {program : Complexity.Language.Program signatures}
variable {stmt : Complexity.Language.Stmt signatures Γ result}
variable {entry : Complexity.Language.State Γ}
variable {bound bound' : Nat}

/-- Weaken a bound on the same observed computation. -/
theorem mono (h : StmtCostBound program stmt entry bound) (budget : bound ≤ bound') :
    StmtCostBound program stmt entry bound' := by
  intro w depth finish control execution steps cost
  exact Nat.le_trans (h execution cost) budget

/-- An empty source statement emits no core instructions. -/
theorem skip (entry : Complexity.Language.State Γ) :
    StmtCostBound program (.skip : Complexity.Language.Stmt signatures Γ result) entry 0 := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- Assignment pays for the primitive's actual emitted fields and updates its
existing lexical target. The observation retains that changed source state;
this bound does not re-prove ranges or give self-copies an unproved discount. -/
theorem assign {τ : Ty} (target : Var Γ τ) (value : Prim Γ τ)
    (entry : Complexity.Language.State Γ) :
    StmtCostBound program (.assign target value : Complexity.Language.Stmt signatures Γ result)
      entry (primCodeSize value) := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- Return accounting includes the actual result fields and private return flag. -/
theorem ret (value : Atom Γ result) (entry : Complexity.Language.State Γ) :
    StmtCostBound program (.ret value) entry (2 * fieldCount result + 2) := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- A binding charges its compiled primitive and continues at its actual
mathematical value. No range or termination proof is required for this bound. -/
theorem letPrim {τ : Ty} (value : Prim Γ τ)
    {continuation : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (body : StmtCostBound program continuation
      (Complexity.Language.State.cons (value.eval entry.locals) entry) bound) :
    StmtCostBound program (.letPrim value continuation) entry (primCodeSize value + bound) := by
  intro w depth finish control execution steps cost
  cases cost with
  | letPrim tail => exact Nat.add_le_add_left (body _ tail) _

/-- A read continues with the cell obtained from the current heap. A bound may
use that read equation without re-establishing validity, ranges or termination. -/
theorem read {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    {nextBound : CellValue kind → Nat}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtCostBound program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) (nextBound value))
    (combine : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      readCodeSize + nextBound value ≤ bound) :
    StmtCostBound program (.read buffer index continuation) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @read Γ result kind depth buffer index continuation entry finish control value
      bufferFits indexFits loaded valueFits bodyExec steps tail =>
      exact (Nat.add_le_add_left (body value loaded bodyExec tail) _).trans
        (combine value loaded)

/-- A uniform numeric continuation bound may still use the actual successful
read equation. This retains mathematical information about a child index or
array element without repeating its validity or termination proof. -/
theorem read_of_success {kind : CellTy} {buffer : Atom Γ (.buffer kind)}
    {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value,
      entry.heap.read (buffer.eval entry.locals) (index.eval entry.locals) = .ok value →
      StmtCostBound program continuation
        (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtCostBound program (.read buffer index continuation) entry (readCodeSize + bound) :=
  read (nextBound := fun _ => bound) body (fun _ _ => Nat.le_refl _)

/-- A uniform read-continuation bound needs no contents specification. -/
theorem read_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {index : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (kind.toTy :: Γ) result}
    (body : ∀ value, StmtCostBound program continuation
      (Complexity.Language.State.cons (kind.toValue value) entry) bound) :
    StmtCostBound program (.read buffer index continuation) entry (readCodeSize + bound) :=
  read_of_success (fun value _ => body value)

/-- A node read charges its three actual field loads and continues with the
head and shared tail returned by the current heap's typed lookup. -/
theorem readNode {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    {nextBound : CellValue kind → Option (NodeRef kind) → Nat}
    (body : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      StmtCostBound program continuation
        (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) entry) (nextBound head tail))
    (combine : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      readNodeCodeSize + nextBound head tail ≤ bound) :
    StmtCostBound program (.readNode ref continuation) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @readNode Γ result kind depth ref continuation entry finish control head tail
      found valueFits bodyExec steps bodyCost =>
      exact (Nat.add_le_add_left (body head tail found bodyExec bodyCost) _).trans
        (combine head tail found)

/-- A uniform node-read continuation bound may retain the actual lookup equation. -/
theorem readNode_of_success {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    (body : ∀ head tail,
      entry.heap.node? kind (ref.eval entry.locals).object = some (head, tail) →
      StmtCostBound program continuation
        (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
          (kind.toValue head, tail) entry) bound) :
    StmtCostBound program (.readNode ref continuation) entry (readNodeCodeSize + bound) :=
  readNode (nextBound := fun _ _ => bound) body (fun _ _ _ => Nat.le_refl _)

/-- A uniform node-read bound needs no extra contents or lifetime contract. -/
theorem readNode_uniform {kind : CellTy} {ref : Atom Γ (.node kind)}
    {continuation : Complexity.Language.Stmt signatures
      (.prod kind.toTy (.option (.node kind)) :: Γ) result}
    (body : ∀ head tail, StmtCostBound program continuation
      (Complexity.Language.State.cons (τ := .prod kind.toTy (.option (.node kind)))
        (kind.toValue head, tail) entry) bound) :
    StmtCostBound program (.readNode ref continuation) entry (readNodeCodeSize + bound) :=
  readNode_of_success (fun head tail _ => body head tail)

/-- An actual successful store pays for its emitted address, value and store
instructions. Its changed heap is already part of the observed execution. -/
theorem write {kind : CellTy} (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat)
    (value : Atom Γ kind.toTy) (entry : Complexity.Language.State Γ) :
    StmtCostBound program (.write buffer index value : Complexity.Language.Stmt signatures Γ result)
      entry writeCodeSize := by
  intro w depth finish control execution steps cost
  cases cost
  exact Nat.le_refl _

/-- Slice accounting follows the actual returned view, without copying its
contents or charging a host allocation. The slice equation can inform the bound. -/
theorem slice {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    {nextBound : Buffer kind → Nat}
    (body : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view →
      StmtCostBound program continuation
        (Complexity.Language.State.cons view entry) (nextBound view))
    (combine : ∀ view, (buffer.eval entry.locals).slice (offset.eval entry.locals)
      (length.eval entry.locals) = .ok view → sliceCodeSize + nextBound view ≤ bound) :
    StmtCostBound program (.slice buffer offset length continuation) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @slice Γ result kind depth buffer offset length continuation entry finish control view
      bufferFits offsetFits lengthFits sliced viewFits bodyExec steps tail =>
      exact (Nat.add_le_add_left (body view sliced bodyExec tail) _).trans
        (combine view sliced)

/-- A uniform slice-continuation bound needs no additional result contract. -/
theorem slice_uniform {kind : CellTy} {buffer : Atom Γ (.buffer kind)} {offset length : Atom Γ .nat}
    {continuation : Complexity.Language.Stmt signatures (.buffer kind :: Γ) result}
    (body : ∀ view, StmtCostBound program continuation
      (Complexity.Language.State.cons view entry) bound) :
    StmtCostBound program (.slice buffer offset length continuation) entry (sliceCodeSize + bound) :=
  slice (nextBound := fun _ => bound) (fun view _ => body view) (fun _ _ => Nat.le_refl _)

/-- A branch bound uses the actual guard decision. The true path includes the
extra jump past the unselected branch; neither path charges the other's body. -/
theorem ite {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesCost : condition.eval entry.locals = true → StmtCostBound program yes entry yesBound)
    (noCost : condition.eval entry.locals = false → StmtCostBound program no entry noBound) :
    StmtCostBound program (.ite condition yes no) entry
      (if condition.eval entry.locals then yesBound + 3 else noBound + 2) := by
  intro w depth finish control execution steps cost
  cases cost with
  | @iteTrue Γ result depth condition yes no entry finish control test body steps bodyCost =>
      simpa only [test, ↓reduceIte] using Nat.add_le_add_right (yesCost test body bodyCost) 3
  | @iteFalse Γ result depth condition yes no entry finish control test body steps bodyCost =>
      simpa only [test, Bool.false_eq_true, ↓reduceIte] using
        Nat.add_le_add_right (noCost test body bodyCost) 2

/-- A proved true guard requires a bound only for the selected branch. -/
theorem ite_true {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    (test : condition.eval entry.locals = true)
    (body : StmtCostBound program yes entry bound) :
    StmtCostBound program (.ite condition yes no) entry (bound + 3) := by
  have selected : StmtCostBound program (.ite condition yes no) entry
      (if condition.eval entry.locals then bound + 3 else 0 + 2) := by
    apply ite (yesBound := bound) (noBound := 0)
    · intro _
      exact @body
    · intro impossible
      have mismatch : true = false := test.symm.trans impossible
      cases mismatch
  simp only [test, ↓reduceIte] at selected
  exact @selected

/-- A proved false guard requires a bound only for the selected branch. -/
theorem ite_false {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result}
    (test : condition.eval entry.locals = false)
    (body : StmtCostBound program no entry bound) :
    StmtCostBound program (.ite condition yes no) entry (bound + 2) := by
  have selected : StmtCostBound program (.ite condition yes no) entry
      (if condition.eval entry.locals then 0 + 3 else bound + 2) := by
    apply ite (yesBound := 0) (noBound := bound)
    · intro impossible
      have mismatch : false = true := test.symm.trans impossible
      cases mismatch
    · intro _
      exact @body
  simp only [test, Bool.false_eq_true, ↓reduceIte] at selected
  exact @selected

/-- A branch-independent upper bound uses the larger of the two already
justified path charges. It need not recover the branch's mathematical result. -/
theorem ite_max {condition : Atom Γ .bool}
    {yes no : Complexity.Language.Stmt signatures Γ result} {yesBound noBound : Nat}
    (yesCost : StmtCostBound program yes entry yesBound)
    (noCost : StmtCostBound program no entry noBound) :
    StmtCostBound program (.ite condition yes no) entry
      (max (yesBound + 3) (noBound + 2)) := by
  apply StmtCostBound.mono (ite (condition := condition) (fun _ => yesCost) (fun _ => noCost))
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_max_right _ _

/-- Option matching preserves the actual selected payload for a dependent
branch bound. The `some` path pays for every copied payload field and its jump;
the `none` path neither reads nor manufactures a payload. -/
theorem matchOption {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {noneBound : Nat} {someBound : Value τ → Nat}
    (noneCost : value.eval entry.locals = none →
      StmtCostBound program noneBranch entry noneBound)
    (someCost : ∀ payload, value.eval entry.locals = some payload →
      StmtCostBound program someBranch (Complexity.Language.State.cons payload entry)
        (someBound payload))
    (noneBounded : value.eval entry.locals = none → noneBound + 2 ≤ bound)
    (someBounded : ∀ payload, value.eval entry.locals = some payload →
      2 * fieldCount τ + someBound payload + 3 ≤ bound) :
    StmtCostBound program (.matchOption value noneBranch someBranch) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @matchNone Γ result τ depth value noneBranch someBranch entry finish control
      selected body steps bodyCost =>
      exact (Nat.add_le_add_right (noneCost selected body bodyCost) 2).trans
        (noneBounded selected)
  | @matchSome Γ result τ depth value noneBranch someBranch entry payload finish control
      selected payloadFits body steps bodyCost =>
      exact (Nat.add_le_add_right
        (Nat.add_le_add_left (someCost payload selected body bodyCost) _) 3).trans
          (someBounded payload selected)

/-- A known absent value requires a bound only for the `none` branch. -/
theorem match_none {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = none)
    (body : StmtCostBound program noneBranch entry bound) :
    StmtCostBound program (.matchOption value noneBranch someBranch) entry (bound + 2) := by
  intro w depth finish control execution steps cost
  cases cost with
  | matchNone bodyCost => exact Nat.add_le_add_right (body _ bodyCost) 2
  | matchSome bodyCost => simp_all

/-- A known present value binds its actual payload and charges its field copies. -/
theorem match_some {τ : Ty} {value : Atom Γ (.option τ)} {payload : Value τ}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    (selected : value.eval entry.locals = some payload)
    (body : StmtCostBound program someBranch
      (Complexity.Language.State.cons payload entry) bound) :
    StmtCostBound program (.matchOption value noneBranch someBranch) entry
      (2 * fieldCount τ + bound + 3) := by
  intro w depth finish control execution steps cost
  cases cost with
  | matchNone bodyCost => simp_all
  | @matchSome Γ result τ depth value noneBranch someBranch entry actual finish control
      same payloadFits branch steps bodyCost =>
      cases Option.some.inj (selected.symm.trans same)
      exact Nat.add_le_add_right (Nat.add_le_add_left (body branch bodyCost) _) 3

/-- A uniform match bound retains the selection equation in both branch proofs. -/
theorem match_max {τ : Ty} {value : Atom Γ (.option τ)}
    {noneBranch : Complexity.Language.Stmt signatures Γ result}
    {someBranch : Complexity.Language.Stmt signatures (τ :: Γ) result}
    {noneBound someBound : Nat}
    (noneCost : value.eval entry.locals = none →
      StmtCostBound program noneBranch entry noneBound)
    (someCost : ∀ payload, value.eval entry.locals = some payload →
      StmtCostBound program someBranch (Complexity.Language.State.cons payload entry) someBound) :
    StmtCostBound program (.matchOption value noneBranch someBranch) entry
      (max (noneBound + 2) (2 * fieldCount τ + someBound + 3)) :=
  matchOption (someBound := fun _ => someBound) noneCost someCost
    (fun _ => Nat.le_max_left _ _) (fun _ _ => Nat.le_max_right _ _)

/-- Reuse a property of an actual normal first execution to bound the second
statement at that execution's final state. The property can come from an existing
source specification; no first-statement termination or repeated contents proof
is required. Early return skips the second statement and pays only its dispatch. -/
theorem seq_of_post {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound : Nat} {post : Complexity.Language.State Γ → Prop}
    {nextBound : Complexity.Language.State Γ → Nat}
    (head : StmtCostBound program first entry firstBound)
    (finished : ∀ {middle},
      Complexity.Language.Exec program first entry middle .normal → post middle)
    (tail : ∀ middle, post middle → StmtCostBound program second middle (nextBound middle))
    (combine : ∀ middle, post middle → firstBound + 2 + nextBound middle ≤ bound)
    (earlyReturn : firstBound + 3 ≤ bound) :
    StmtCostBound program (.seq first second) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @seqNormal Γ result depth first second entry middle finish control
      firstExec secondExec firstSteps secondSteps firstCost secondCost =>
      have property := finished firstExec.erase
      exact (Nat.add_le_add (Nat.add_le_add_right (head firstExec firstCost) 2)
        (tail middle property secondExec secondCost)).trans (combine middle property)
  | seqReturn firstCost =>
      exact (Nat.add_le_add_right (head _ firstCost) 3).trans earlyReturn

/-- A uniformly bounded continuation composes without an intermediate
correctness proof. Normal continuation pays two guard instructions and executes
the tail; early return pays three guard/jump instructions and skips the tail. -/
theorem seq {first second : Complexity.Language.Stmt signatures Γ result}
    {firstBound secondBound : Nat}
    (head : StmtCostBound program first entry firstBound)
    (tail : ∀ middle, StmtCostBound program second middle secondBound) :
    StmtCostBound program (.seq first second) entry
      (firstBound + max (2 + secondBound) 3) := by
  apply seq_of_post (post := fun _ => True) (nextBound := fun _ => secondBound)
    head (fun _ => trivial) (fun middle _ => tail middle)
  · intro middle property
    simpa only [Nat.add_assoc] using Nat.add_le_add_left (Nat.le_max_left (2 + secondBound) 3)
      firstBound
  · exact Nat.add_le_add_left (Nat.le_max_right (2 + secondBound) 3) firstBound

/-- A potential bounds an effectful loop over the same existing execution.
Every guard runs at the current state, and its actual final state starts the
body. A normal round preserves the invariant and pays from the decrease of the
potential; the final false guard and an early return have their own exit bounds.
The transition premises may reuse consequences of source specifications. They
do not require another correctness, termination or representation proof. -/
theorem «while» {guard : Complexity.Language.Stmt signatures Γ .bool}
    {body : Complexity.Language.Stmt signatures Γ result}
    {invariant : Complexity.Language.State Γ → Prop}
    {potential guardBound : Complexity.Language.State Γ → Nat}
    {bodyBound : Complexity.Language.State Γ → Complexity.Language.State Γ → Nat}
    (guardCost : ∀ state, invariant state →
      StmtCostBound program guard state (guardBound state))
    (bodyCost : ∀ state afterGuard, invariant state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      StmtCostBound program body afterGuard (bodyBound state afterGuard))
    (preserve : ∀ state afterGuard afterBody, invariant state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal → invariant afterBody)
    (falseExit : ∀ state afterGuard, invariant state →
      Complexity.Language.Exec program guard state afterGuard (.returned false) →
      guardBound state + 11 ≤ potential state)
    (normalStep : ∀ state afterGuard afterBody, invariant state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard afterBody .normal →
      guardBound state + bodyBound state afterGuard + potential afterBody + 10 ≤ potential state)
    (returnExit : ∀ state afterGuard finish value, invariant state →
      Complexity.Language.Exec program guard state afterGuard (.returned true) →
      Complexity.Language.Exec program body afterGuard finish (.returned value) →
      guardBound state + bodyBound state afterGuard + 17 ≤ potential state)
    (initial : invariant entry) :
    StmtCostBound program (.while guard body) entry (potential entry) := by
  intro w depth finish control execution steps cost
  have loopBound : ∀ n {state finish : Complexity.Language.State Γ} {control : Control result}
      (execution : RealizedExec program w depth (.while guard body) state finish control),
      ExecutionCost execution n → invariant state → n ≤ potential state := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro state finish control execution cost hstate
        cases cost with
        | @whileFalse Γ result depth guard body state finish test guardSteps testCost =>
            have guardLe := guardCost state hstate test testCost
            have exitLe := falseExit state finish hstate test.erase
            omega
        | @whileTrue Γ result depth guard body state afterGuard afterBody finish control
            test iteration rest guardSteps bodySteps restSteps testCost iterationCost restCost =>
            have guardLe := guardCost state hstate test testCost
            have bodyLe := bodyCost state afterGuard hstate test.erase iteration iterationCost
            have nextInvariant := preserve state afterGuard afterBody hstate
              test.erase iteration.erase
            have restLe := ih restSteps (by omega) rest restCost nextInvariant
            have roundLe := normalStep state afterGuard afterBody hstate
              test.erase iteration.erase
            omega
        | @whileReturn Γ result depth guard body state afterGuard finish value
            test iteration guardSteps bodySteps testCost iterationCost =>
            have guardLe := guardCost state hstate test testCost
            have bodyLe := bodyCost state afterGuard hstate test.erase iteration iterationCost
            have exitLe := returnExit state afterGuard finish value hstate
              test.erase iteration.erase
            omega
  exact loopBound steps execution cost initial

/-- Compose a separate callee bound with its actual returned-value and heap continuation.
The result premise concerns only completed source calls: use an existing
`FunctionTotal.postcondition`, or `True` when the bound needs no result property.
It does not require termination, expose a callee environment to the caller, or
charge the callee's body wrapper twice. -/
theorem call {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {pre : Env signatures[fn].params → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat}
    {post : Value signatures[fn].result → Heap → Prop}
    {nextBound : Value signatures[fn].result → Heap → Nat}
    (callee : FunctionCostBound program fn pre calleeBound)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (returned : ∀ {finish value},
      Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) finish (.returned value) → post value finish.heap)
    (body : ∀ value heap, post value heap →
      StmtCostBound program continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post value heap →
      callCost program fn (calleeBound (args.eval entry.locals) entry.heap) +
        nextBound value heap ≤ bound) :
    StmtCostBound program (.call fn args continuation) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
      arguments calleeExec bodyExec calleeSteps bodySteps calleeCost bodyCost =>
      have property := returned calleeExec.erase
      have calleeLe := callee _ _ hpre calleeExec calleeCost
      have bodyLe := body _ _ property bodyExec bodyCost
      exact Nat.le_trans
        (Nat.add_le_add (callCost_mono program fn calleeLe) bodyLe)
        (combine _ _ property)

/-- A continuation with a uniform bound needs no mathematical result contract.
The callee's proved cost and the actual compiler-derived call charge suffice. -/
theorem call_uniform {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {pre : Env signatures[fn].params → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat}
    {nextBound : Nat}
    (callee : FunctionCostBound program fn pre calleeBound)
    (hpre : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, StmtCostBound program continuation
      (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtCostBound program (.call fn args continuation) entry
      (callCost program fn (calleeBound (args.eval entry.locals) entry.heap) + nextBound) :=
  call (post := fun _ _ => True) (nextBound := fun _ _ => nextBound) callee hpre
    (fun _ => trivial) (fun value heap _ => body value heap) (fun _ _ _ => Nat.le_refl _)

/-- A supplied source contract connects the actual returned value and heap to
a dependent continuation bound. The final comparison uses that same proven
postcondition; it need not bound impossible callee outcomes. -/
theorem call_of_spec_le {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {costPre pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat}
    {nextBound : Value signatures[fn].result → Heap → Nat}
    (callee : FunctionCostBound program fn costPre calleeBound)
    (specification : FunctionTotal program fn pre post)
    (costInput : costPre (args.eval entry.locals) entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (nextCost : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtCostBound program continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) (nextBound value heap))
    (combine : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      callCost program fn (calleeBound (args.eval entry.locals) entry.heap) +
        nextBound value heap ≤ bound) :
    StmtCostBound program (.call fn args continuation) entry bound := by
  apply call (post := post (args.eval entry.locals) entry.heap)
    (nextBound := nextBound) callee costInput
  · intro finish value executed
    exact specification.postcondition input executed
  · exact nextCost
  · exact combine

/-- Reuse a supplied source contract while inferring a uniform continuation
bound. Uniformity concerns the cost bound, not the returned value, heap or
postcondition: the continuation retains all actual callee effects. -/
theorem call_of_spec {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {continuation : Complexity.Language.Stmt signatures (signatures[fn].result :: Γ) result}
    {costPre pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat} {nextBound : Nat}
    (callee : FunctionCostBound program fn costPre calleeBound)
    (specification : FunctionTotal program fn pre post)
    (costInput : costPre (args.eval entry.locals) entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtCostBound program continuation
        (Complexity.Language.State.cons value ⟨entry.locals, heap⟩) nextBound) :
    StmtCostBound program (.call fn args continuation) entry
      (callCost program fn (calleeBound (args.eval entry.locals) entry.heap) + nextBound) :=
  call_of_spec_le (nextBound := fun _ _ => nextBound) callee specification costInput input body
    (fun _ _ _ => Nat.le_refl _)

/-- A standalone call resumes the next statement with the caller's locals and
the callee's actual final heap. Its supplied contract transports contents and
frame facts to the next cost proof, without exposing call/skip execution cases.
The empty result scope cannot return from the caller, so only the real normal
sequence dispatch is charged. Callee initialization is already in its bound. -/
theorem call_seq {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {second : Complexity.Language.Stmt signatures Γ result}
    {costPre pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat}
    {nextBound : Value signatures[fn].result → Heap → Nat}
    (callee : FunctionCostBound program fn costPre calleeBound)
    (specification : FunctionTotal program fn pre post)
    (costInput : costPre (args.eval entry.locals) entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtCostBound program second ⟨entry.locals, heap⟩ (nextBound value heap))
    (combine : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      callCost program fn (calleeBound (args.eval entry.locals) entry.heap) + 2 +
        nextBound value heap ≤ bound) :
    StmtCostBound program (.seq (.call fn args .skip) second) entry bound := by
  intro w depth finish control execution steps cost
  cases cost with
  | @seqNormal Γ result depth first second entry middle finish control
      firstExec secondExec firstSteps secondSteps firstCost secondCost =>
      cases firstCost with
      | @callReturn Γ result depth fn args continuation entry calleeFinish value finish control
          arguments calleeExec bodyExec calleeSteps bodySteps calleeCost bodyCost =>
          cases bodyCost
          have property := specification.postcondition input calleeExec.erase
          have calleeLe := callCost_mono program fn
            (callee _ _ costInput calleeExec calleeCost)
          have tailLe := body value calleeFinish.heap property secondExec secondCost
          have totalLe := combine value calleeFinish.heap property
          simpa only [Nat.add_zero] using
            (Nat.add_le_add (Nat.add_le_add_right calleeLe 2) tailLe).trans totalLe
  | seqReturn firstCost =>
      cases firstCost with
      | callReturn calleeCost bodyCost => cases bodyCost

/-- Infer the structural bound for a standalone call and a uniformly bounded
next statement, retaining the supplied callee's actual postcondition. This
specializes `call_seq`; it neither assumes unchanged memory nor repeats the
callee's correctness or instruction accounting. -/
theorem call_seq_uniform {fn : Fin signatures.length} {args : Args Γ signatures[fn].params}
    {second : Complexity.Language.Stmt signatures Γ result}
    {costPre pre : Env signatures[fn].params → Heap → Prop}
    {post : Env signatures[fn].params → Heap → Value signatures[fn].result → Heap → Prop}
    {calleeBound : Env signatures[fn].params → Heap → Nat} {nextBound : Nat}
    (callee : FunctionCostBound program fn costPre calleeBound)
    (specification : FunctionTotal program fn pre post)
    (costInput : costPre (args.eval entry.locals) entry.heap)
    (input : pre (args.eval entry.locals) entry.heap)
    (body : ∀ value heap, post (args.eval entry.locals) entry.heap value heap →
      StmtCostBound program second ⟨entry.locals, heap⟩ nextBound) :
    StmtCostBound program (.seq (.call fn args .skip) second) entry
      (callCost program fn (calleeBound (args.eval entry.locals) entry.heap) + 2 + nextBound) :=
  call_seq (nextBound := fun _ _ => nextBound) callee specification costInput input body
    (fun _ _ _ => Nat.le_refl _)

end StmtCostBound

namespace FunctionCostBound

/-- A bound on the source body yields a bound on the complete lowered function
body, adding its return-flag initialization exactly once. This is
still conditional on a realized returned execution, not a termination claim. -/
theorem of_stmt {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {coreBound : Env signatures[fn].params → Heap → Nat}
    (body : ∀ args heap, pre args heap →
      StmtCostBound program (program.body fn) ⟨args, heap⟩ (coreBound args heap)) :
    FunctionCostBound program fn pre (fun args heap => coreBound args heap + 2) := by
  intro args heap hpre w depth finish value execution steps cost
  exact Nat.add_le_add_right (body args heap hpre execution cost) 2

/-- Infer a core bound after introducing ordinary arguments, then compare its
complete returning-body charge with the requested function bound. This avoids
asking the author to choose a separate bound function for every source scope. -/
theorem of_pointwise {signatures : List Signature}
    {program : Complexity.Language.Program signatures} {fn : Fin signatures.length}
    {pre : Env signatures[fn].params → Heap → Prop}
    {bound : Env signatures[fn].params → Heap → Nat}
    (body : ∀ args heap, pre args heap → ∃ core,
      StmtCostBound program (program.body fn) ⟨args, heap⟩ core ∧ core + 2 ≤ bound args heap) :
    FunctionCostBound program fn pre bound := by
  intro args heap hpre w depth finish value execution steps cost
  obtain ⟨core, certificate, budget⟩ := body args heap hpre
  exact (Nat.add_le_add_right (certificate execution cost) 2).trans budget

end FunctionCostBound

end Ram.LanguageCompiler
