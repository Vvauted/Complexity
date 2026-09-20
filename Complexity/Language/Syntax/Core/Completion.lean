/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.LocalReturn
import Complexity.Language.Eval.Locals.LocalReturn.While
import Complexity.Language.Eval.Locals.Effects

/-!
# Generated local-completion views and contracts

Constructs visible-local completion coordinates and their contracts for local-return blocks,
scratch scopes and loops. Private result slots stay in actual execution and cleanup; generated
projections and frames connect the author-facing proof view to that complete state.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

/-- Completion coordinates are projections of the existing full source locals.
They do not define another observer or remove roots from scratch execution. -/
def completionDeclarations (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM (Array Syntax) := do
  let some target := site.localReturn | return #[]
  let (targetBinding, targetIndex) ← lookupProofBinding site.scope target.pending
  unless targetBinding.privatePending do
    Macro.throwErrorAt site.name "a local completion target must retain its compiler-slot identity"
  let visibleScope := site.scope.filter (! ·.privatePending)
  let locals := loopMember site "Locals"
  let visibleType := loopMember site "Visible"
  let visible := loopMember site "visible"
  let pending := loopMember site "pending"
  let entry := loopMember site "entry"
  let reconstruct := loopMember site "reconstruct"
  let visibleEntry := loopMember site "visible_entry"
  let pendingEntry := loopMember site "pending_entry"
  let visibleReconstruct := loopMember site "visible_reconstruct"
  let pendingReconstruct := loopMember site "pending_reconstruct"
  let reconstructNone := loopMember site "reconstruct_none"
  let visibleValue ← freshProofName site.name `visible
  let fullValue ← freshProofName site.name `locals
  let initialValue ← freshProofName site.name `initial
  let pendingValue ← freshProofName site.name `pending
  let visibleValueType ← scopeValueTypes visibleScope
  let pendingType ← valueTypeTerm (.option target.type)
  let fullFields ← tupleFields site.scope ⟨fullValue.raw⟩
  let initialFields ← tupleFields site.scope ⟨initialValue.raw⟩
  let visibleFields ← tupleFields visibleScope ⟨visibleValue.raw⟩
  let mut selected := #[]
  let mut initialized := #[]
  let mut restored := #[]
  let mut position := 0
  for (binding, index) in site.scope.zipIdx do
    if binding.privatePending then
      initialized := initialized.push (← `(none))
      restored := restored.push (if binding.proofName.getId == target.pending then
        ⟨pendingValue.raw⟩ else initialFields[index]!)
    else
      selected := selected.push fullFields[index]!
      initialized := initialized.push visibleFields[position]!
      restored := restored.push visibleFields[position]!
      position := position + 1
  let selectedTuple ← fieldsTuple selected
  let initializedTuple ← fieldsTuple initialized
  let restoredTuple ← fieldsTuple restored
  let visibleEta ← tupleExtProof visibleScope
  let mut declarations := #[
    (← `(command| /-- Source-visible locals, without compiler completion slots. -/
      abbrev $visibleType:ident := $visibleValueType)).raw,
    (← `(command| /-- Project source-visible coordinates from the unchanged full locals. -/
      abbrev $visible:ident ($fullValue:ident : $locals:ident) : $visibleType:ident :=
        $selectedTuple)).raw,
    (← `(command| /-- The current local result; actual source control is unchanged. -/
      abbrev $pending:ident ($fullValue:ident : $locals:ident) : $pendingType :=
        $(fullFields[targetIndex]!))).raw,
    (← `(command| /-- Enter this source boundary with empty private completion slots. -/
      abbrev $entry:ident ($visibleValue:ident : $visibleType:ident) : $locals:ident :=
        $initializedTuple)).raw,
    (← `(command| /-- Restore the same full locals, retaining the ancestor slots from entry. -/
      abbrev $reconstruct:ident ($initialValue:ident : $locals:ident)
          ($pendingValue:ident : $pendingType) ($visibleValue:ident : $visibleType:ident) :
          $locals:ident := $restoredTuple)).raw,
    (← `(command| theorem $visibleEntry:ident ($visibleValue:ident : $visibleType:ident) :
        $visible:ident ($entry:ident $visibleValue:ident) = $visibleValue:ident :=
      $visibleEta)).raw,
    (← `(command| theorem $pendingEntry:ident ($visibleValue:ident : $visibleType:ident) :
        $pending:ident ($entry:ident $visibleValue:ident) = none := rfl)).raw,
    (← `(command| theorem $visibleReconstruct:ident ($initialValue:ident : $locals:ident)
        ($pendingValue:ident : $pendingType) ($visibleValue:ident : $visibleType:ident) :
        $visible:ident ($reconstruct:ident $initialValue:ident $pendingValue:ident $visibleValue:ident) =
          $visibleValue:ident := $visibleEta)).raw,
    (← `(command| theorem $pendingReconstruct:ident ($initialValue:ident : $locals:ident)
        ($pendingValue:ident : $pendingType) ($visibleValue:ident : $visibleType:ident) :
        $pending:ident ($reconstruct:ident $initialValue:ident $pendingValue:ident $visibleValue:ident) =
          $pendingValue:ident := rfl)).raw,
    (← `(command| /-- Continuing completion coordinates recover the same full entry. -/
      theorem $reconstructNone:ident ($initialValue:ident $visibleValue:ident : $visibleType:ident) :
        $reconstruct:ident ($entry:ident $initialValue:ident) none $visibleValue:ident =
          $entry:ident $visibleValue:ident := rfl)).raw]
  let codeNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let definitions := codeNames ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.LocalReturn.store, ``Complexity.Language.Stmt.LocalReturn.resume,
      ``Complexity.Language.Stmt.LocalReturn.guard])
  let noReturnArgs := definitions ++ (← constantSimpArgs #[``Complexity.Language.Stmt.NoReturn])
  let frameArgs := definitions ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.PreservesLocal, ``Complexity.Language.Var.index])
  let types ← scopeTypes site.scope
  let result ← typeTerm site.result
  let targetType ← typeTerm target.type
  let view := loopMember site "View"
  let viewApply := loopMember site "view_apply"
  let viewSymmApply := loopMember site "view_symm_apply"
  let pendingEval := loopMember site "pending_eval"
  declarations := declarations.push (← `(command|
    /-- The completion observation is the actual source slot read. -/
    theorem $pendingEval:ident ($fullValue:ident : $locals:ident) :
        (Complexity.Language.Atom.var $(← variableTerm targetIndex) :
          Complexity.Language.Atom $types (.option $targetType)).eval
            (($view:ident).symm $fullValue:ident) = $pending:ident $fullValue:ident := by
      simp only [$viewSymmApply:ident, $pending:ident,
        Complexity.Language.Atom.eval, Complexity.Language.Env.cons_here,
        Complexity.Language.Env.cons_there])).raw
  let visibleRooted := loopMember site "VisibleRooted"
  let scopeSafeReconstruct := loopMember site "scopeSafe_reconstruct"
  let rootHeap ← freshProofName site.name `rootHeap
  let finalHeap ← freshProofName site.name `finalHeap
  let rootStart ← freshProofName site.name `start
  let mut rootConditions ← `(True)
  for (binding, field) in (visibleScope.toArray.zip visibleFields).reverse do
    rootConditions ← `(Complexity.Language.ValueRooted $rootHeap:ident
      (τ := $(← typeTerm binding.type)) $field ∧ $rootConditions)
  declarations := declarations.push (← `(command|
    /-- The source-visible values retain only roots from this heap. -/
    def $visibleRooted:ident ($rootHeap:ident : Complexity.Language.Heap)
        ($visibleValue:ident : $visibleType:ident) : Prop := $rootConditions)).raw
  declarations := declarations.push (← `(command|
    /-- The original full scratch safety condition after actual frame restoration.
    Ancestor slots are empty at entry; the current completion remains a checked root. -/
    theorem $scopeSafeReconstruct:ident
        ($rootHeap:ident $finalHeap:ident : Complexity.Language.Heap)
        ($rootStart:ident $visibleValue:ident : $visibleType:ident)
        ($pendingValue:ident : $pendingType) :
        Complexity.Language.ScopeSafe $rootHeap:ident
          ⟨($view:ident).symm
            ($reconstruct:ident ($entry:ident $rootStart:ident)
              $pendingValue:ident $visibleValue:ident), $finalHeap:ident⟩
          (.normal : Complexity.Language.Control $result) ↔
        $visibleRooted:ident $rootHeap:ident $visibleValue:ident ∧
          Complexity.Language.ValueRooted $rootHeap:ident
            (τ := .option $targetType) $pendingValue:ident := by
      simp [Complexity.Language.ScopeSafe, $viewSymmApply:ident,
        $reconstruct:ident, $entry:ident, $visibleRooted:ident,
        Complexity.Language.Env.Rooted.cons_iff, Complexity.Language.Env.Rooted.empty,
        Complexity.Language.ValueRooted, Complexity.Language.Control.Rooted,
        and_assoc, and_left_comm, and_comm])).raw
  for (suffix, codeSuffix) in [("body_", "Body"), ("", "Code")] do
    let code := loopMember site codeSuffix
    let noReturn := loopMember site (suffix ++ "noReturn")
    declarations := declarations.push (← `(command|
      /-- Local completion does not produce an enclosing source return. -/
      theorem $noReturn:ident : ( $code:ident ).NoReturn := by
        simp [$noReturnArgs,*])).raw
    let frame := loopMember site (suffix ++ "ancestor_pending_frame")
    let before ← freshProofName site.name `before
    let after ← freshProofName site.name `after
    let control ← freshProofName site.name `control
    let execution ← freshProofName site.name `execution
    let mut facts := #[]
    let mut tactics : Array (TSyntax `tactic) := #[]
    for (binding, index) in site.scope.zipIdx do
      if binding.privatePending && binding.proofName.getId != target.pending then
        let fixed ← freshProofName site.name `ancestorPending
        let sourceVar ← variableTerm index
        facts := facts.push fixed
        tactics := tactics.push (← `(tactic|
          have $fixed:ident := Complexity.Language.Exec.get_eq $execution:ident $sourceVar
            (by simp [$frameArgs,*])))
    let frameSimpArgs ← namedSimpArgs (#[reconstruct, pending, visible, viewApply] ++ facts)
    let proofTactics := tactics.push (← `(tactic|
      simp only [$frameSimpArgs,*] <;> exact $(← tupleExtProof site.scope)))
    declarations := declarations.push (← `(command|
      /-- Actual finite execution fixes every ancestor completion slot. This
      restores full locals; it does not discard roots or assume successful cleanup. -/
      theorem $frame:ident {$before:ident $after:ident : Complexity.Language.State $types}
          {$control:ident : Complexity.Language.Control $result}
          ($execution:ident : Complexity.Language.Exec $program:ident $code:ident
            $before:ident $after:ident $control:ident) :
          $reconstruct:ident ($view:ident ($before:ident).locals)
            ($pending:ident ($view:ident ($after:ident).locals))
            ($visible:ident ($view:ident ($after:ident).locals)) =
              $view:ident ($after:ident).locals := by
        $proofTactics:tactic*)).raw
    let contract := loopMember site (suffix ++ "completion_contract")
    let specification := loopMember site (suffix ++ "completion_spec")
    let specificationAt := loopMember site (suffix ++ "completion_spec_at")
    let observation := if suffix.isEmpty then site.name else loopMember site "body"
    let observed := loopMember site (if suffix.isEmpty then "observe" else "body_observe")
    let pre ← freshProofName site.name `pre
    let normal ← freshProofName site.name `normal
    let returned ← freshProofName site.name `returned
    let start ← freshProofName site.name `start
    let heap ← freshProofName site.name `heap
    let output ← freshProofName site.name `output
    let finish ← freshProofName site.name `finish
    let value ← freshProofName site.name `value
    let chosen ← freshProofName site.name `specification
    let post ← freshProofName site.name `post
    let initial ← freshProofName site.name `initial
    let evaluated ← freshProofName site.name `evaluated
    let executed ← freshProofName site.name `executed
    let fixed ← freshProofName site.name `fixed
    let valueType ← valueTypeTerm target.type
    let preType ← `($visibleType:ident → Complexity.Language.Heap → Prop)
    let normalType ← `($visibleType:ident → Complexity.Language.Heap →
      $visibleType:ident → Complexity.Language.Heap → Prop)
    let returnedType ← `($visibleType:ident → Complexity.Language.Heap →
      $valueType → $visibleType:ident → Complexity.Language.Heap → Prop)
    let invocation ← tupleApplication site.scope observation (← `($entry:ident $start:ident))
    let action ← `(fun ($start:ident : $visibleType:ident) => $invocation)
    declarations := declarations.push (← `(command|
      /-- Author relations use visible locals and actual endpoint heaps. The
      existing action still returns its full locals and actual source control. -/
      abbrev $contract:ident ($pre:ident : $preType) ($normal:ident : $normalType)
          ($returned:ident : $returnedType) : Prop :=
        Complexity.Language.Stmt.BlockSpec $action $pre:ident
          (fun $start:ident $heap:ident $output:ident $finish:ident =>
            match $pending:ident $output:ident with
            | none => $normal:ident $start:ident $heap:ident ($visible:ident $output:ident) $finish:ident
            | some $value:ident =>
                $returned:ident $start:ident $heap:ident $value:ident
                  ($visible:ident $output:ident) $finish:ident)
          (fun _ _ _ _ _ => False))).raw
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Apply the visible completion contract, reconstructing the full output
      from this same actual execution rather than guessing hidden coordinates. -/
      theorem $specificationAt:ident {$pre:ident : $preType} {$normal:ident : $normalType}
          {$returned:ident : $returnedType}
          ($chosen:ident : $contract:ident $pre:ident $normal:ident $returned:ident)
          ($start:ident : $visibleType:ident)
          ($post:ident : Std.Do.PostCond (Complexity.Language.Control $result × $locals:ident)
            (.arg Complexity.Language.Heap .pure)) :
          Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
            (ps := .arg Complexity.Language.Heap .pure) $invocation
            (fun $heap:ident => ⟨$pre:ident $start:ident $heap:ident ∧
              (∀ $output:ident $finish:ident,
                $normal:ident $start:ident $heap:ident $output:ident $finish:ident →
                  (($post:ident).1 (.normal,
                    $reconstruct:ident ($entry:ident $start:ident) none $output:ident) $finish:ident).down) ∧
              (∀ $value:ident $output:ident $finish:ident,
                $returned:ident $start:ident $heap:ident $value:ident $output:ident $finish:ident →
                  (($post:ident).1 (.normal,
                    $reconstruct:ident ($entry:ident $start:ident) (some $value:ident) $output:ident)
                      $finish:ident).down)⟩) $post:ident := by
        change Complexity.Language.Stmt.BlockSpec $action $pre:ident
          (fun $start:ident $heap:ident $output:ident $finish:ident =>
            match $pending:ident $output:ident with
            | none => $normal:ident $start:ident $heap:ident
                ($visible:ident $output:ident) $finish:ident
            | some $value:ident => $returned:ident $start:ident $heap:ident $value:ident
                ($visible:ident $output:ident) $finish:ident)
          (fun _ _ _ _ _ => False) at $chosen:ident
        refine Complexity.Language.Stmt.LocalReturn.completion_spec (τ := $targetType)
          (result := $result) (action := $action) (pre := $pre:ident)
          (normal := $normal:ident) (returned := $returned:ident)
          $pending:ident $visible:ident ?_ $start:ident
          ($reconstruct:ident ($entry:ident $start:ident)) ?_ $post:ident
        · refine Complexity.Language.Stmt.BlockSpec.mono $chosen:ident
            (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible)
          intro $start:ident $heap:ident $output:ident $finish:ident _ $initial:ident
          cases $evaluated:ident : $pending:ident $output:ident <;>
            simpa only [$evaluated:ident] using $initial:ident
        · intro $heap:ident $output:ident $finish:ident $initial:ident $evaluated:ident
          have $executed:ident : Complexity.Language.Exec $program:ident $code:ident
              ⟨($view:ident).symm ($entry:ident $start:ident), $heap:ident⟩
              ⟨($view:ident).symm $output:ident, $finish:ident⟩ .normal :=
            Complexity.Language.Stmt.observe_eq_some_iff.mp
              (by simpa only [$observed:ident] using $evaluated:ident)
          have $fixed:ident := $frame:ident $executed:ident
          simpa only [Equiv.apply_symm_apply] using $fixed:ident)).raw
    let initialVisible ← scopeTuple visibleScope
    let mut sourceArguments : Array (TSyntax `term) := #[]
    for binding in site.scope do
      let argument ← if binding.privatePending then `(none) else pure ⟨binding.proofName.raw⟩
      sourceArguments := sourceArguments.push argument
    let directAction := Lean.Syntax.mkApp ⟨observation.raw⟩ sourceArguments
    let postType ← `(Std.Do.PostCond (Complexity.Language.Control $result × $locals:ident)
      (.arg Complexity.Language.Heap .pure))
    let directType ← quantifyScope visibleScope (← `(∀ ($post:ident : $postType),
      Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
        (ps := .arg Complexity.Language.Heap .pure) $directAction
        (fun $heap:ident => ⟨$pre:ident $initialVisible $heap:ident ∧
          (∀ $output:ident $finish:ident,
            $normal:ident $initialVisible $heap:ident $output:ident $finish:ident →
              (($post:ident).1 (.normal,
                $reconstruct:ident ($entry:ident $initialVisible) none $output:ident)
                  $finish:ident).down) ∧
          (∀ $value:ident $output:ident $finish:ident,
            $returned:ident $initialVisible $heap:ident $value:ident
              $output:ident $finish:ident →
              (($post:ident).1 (.normal,
                $reconstruct:ident ($entry:ident $initialVisible)
                  (some $value:ident) $output:ident) $finish:ident).down)⟩) $post:ident))
    let directProof ← curryScope visibleScope (← `(fun $post:ident =>
      $specificationAt:ident $chosen:ident $initialVisible $post:ident))
    declarations := declarations.push (← `(command|
      open scoped Part.TotalCorrectness in
      /-- Apply the same completion contract at independently named source inputs.
      The actual action has canonical arguments, so native specification lookup
      does not need to infer a tuple from its projections. -/
      theorem $specification:ident {$pre:ident : $preType} {$normal:ident : $normalType}
          {$returned:ident : $returnedType}
          ($chosen:ident : $contract:ident $pre:ident $normal:ident $returned:ident) :
          $directType := $directProof)).raw
  if site.guard.isSome then return declarations
  let contract := loopMember site "completion_contract"
  let bodyContract := loopMember site "body_completion_contract"
  let bodySpecification := loopMember site "body_completion_spec_at"
  let contractOfBody := loopMember site "completion_contract_of_body"
  let body := loopMember site "Body"
  let code := loopMember site "Code"
  let bodyObserved := loopMember site "body_observe"
  let pre ← freshProofName site.name `pre
  let normal ← freshProofName site.name `normal
  let returned ← freshProofName site.name `returned
  let chosen ← freshProofName site.name `bodySpecification
  let start ← freshProofName site.name `start
  let heap ← freshProofName site.name `heap
  let output ← freshProofName site.name `output
  let finish ← freshProofName site.name `finish
  let value ← freshProofName site.name `value
  let initial ← freshProofName site.name `initial
  let current ← freshProofName site.name `current
  let same ← freshProofName site.name `same
  let property ← freshProofName site.name `property
  let valueType ← valueTypeTerm target.type
  let preType ← `($visibleType:ident → Complexity.Language.Heap → Prop)
  let normalType ← `($visibleType:ident → Complexity.Language.Heap →
    $visibleType:ident → Complexity.Language.Heap → Prop)
  let returnedType ← `($visibleType:ident → Complexity.Language.Heap →
    $valueType → $visibleType:ident → Complexity.Language.Heap → Prop)
  declarations := declarations.push (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Close the actual scratch boundary from visible body relations. Roots
    are checked before reclamation; the author's postcondition uses the heap
    after that same reclamation. Private slots are restored by the body frame. -/
    theorem $contractOfBody:ident {$pre:ident : $preType}
        {$normal:ident : $normalType} {$returned:ident : $returnedType}
        ($chosen:ident : $bodyContract:ident $pre:ident
          (fun $start:ident $heap:ident $output:ident $finish:ident =>
            $visibleRooted:ident $heap:ident $output:ident ∧
              $normal:ident $start:ident $heap:ident $output:ident
                (($finish:ident).take ($heap:ident).objects.size))
          (fun $start:ident $heap:ident $value:ident $output:ident $finish:ident =>
            $visibleRooted:ident $heap:ident $output:ident ∧
              Complexity.Language.ValueRooted $heap:ident (τ := $targetType) $value:ident ∧
              $returned:ident $start:ident $heap:ident $value:ident $output:ident
                (($finish:ident).take ($heap:ident).objects.size))) :
        $contract:ident $pre:ident $normal:ident $returned:ident := by
      change Complexity.Language.Stmt.BlockSpec
        (fun $start:ident => Complexity.Language.Stmt.observe $view:ident $code:ident
          $program:ident ($entry:ident $start:ident)) $pre:ident
        (fun $start:ident $heap:ident $output:ident $finish:ident =>
          match $pending:ident $output:ident with
          | none => $normal:ident $start:ident $heap:ident
              ($visible:ident $output:ident) $finish:ident
          | some $value:ident => $returned:ident $start:ident $heap:ident $value:ident
              ($visible:ident $output:ident) $finish:ident)
        (fun _ _ _ _ _ => False)
      change Complexity.Language.Stmt.BlockSpec
        (fun $start:ident => Complexity.Language.Stmt.observe $view:ident
          (.scope $body:ident) $program:ident ($entry:ident $start:ident)) _ _ _
      refine Complexity.Language.Stmt.BlockSpec.scope $view:ident $program:ident
        $body:ident $entry:ident ?_
      intro $start:ident $heap:ident $initial:ident
      dsimp only
      rw [$bodyObserved:ident]
      refine ($bodySpecification:ident $chosen:ident $start:ident _).mono ?_
        (Std.Do.PostCond.entails.refl _)
      intro $current:ident $same:ident
      subst $current:ident
      refine ⟨$initial:ident, ?_, ?_⟩
      · intro $output:ident $finish:ident $property:ident
        refine ⟨($scopeSafeReconstruct:ident $heap:ident $finish:ident
          $start:ident $output:ident none).mpr ⟨($property:ident).1, trivial⟩, ?_⟩
        simpa only [$pendingReconstruct:ident, $visibleReconstruct:ident]
          using ($property:ident).2
      · intro $value:ident $output:ident $finish:ident $property:ident
        refine ⟨($scopeSafeReconstruct:ident $heap:ident $finish:ident
          $start:ident $output:ident (some $value:ident)).mpr
            ⟨($property:ident).1, ($property:ident).2.1⟩, ?_⟩
        simpa only [$pendingReconstruct:ident, $visibleReconstruct:ident]
          using ($property:ident).2.2)).raw
  return declarations

def loopCompletionDeclarations (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM (Array Syntax) := do
  let some target := site.localReturn | return #[]
  unless site.guard.isSome do return #[]
  let (_, targetIndex) ← lookupProofBinding site.scope target.pending
  let visibleType := loopMember site "Visible"
  let visible := loopMember site "visible"
  let entry := loopMember site "entry"
  let view := loopMember site "View"
  let viewApply := loopMember site "view_apply"
  let viewSymmApply := loopMember site "view_symm_apply"
  let guard := loopMember site "Guard"
  let guardAction := loopMember site "guard"
  let guardFrame := loopMember site "guard_completion_frame"
  let guardCompleted := loopMember site "guard_completed"
  let guardContract := loopMember site "guard_completion_contract"
  let types ← scopeTypes site.scope
  let targetType ← typeTerm target.type
  let targetValue ← valueTypeTerm target.type
  let pendingAtom ← `(Complexity.Language.Atom.var $(← variableTerm targetIndex))
  let preservedArgs ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let preservedArgs := preservedArgs ++ (← constantSimpArgs
    #[``Complexity.Language.Stmt.PreservesLocal, ``Complexity.Language.Var.index,
      ``Complexity.Language.Stmt.LocalReturn.store, ``Complexity.Language.Stmt.LocalReturn.resume,
      ``Complexity.Language.Stmt.LocalReturn.guard])
  let start ← freshProofName site.name `start
  let heap ← freshProofName site.name `heap
  let finish ← freshProofName site.name `finish
  let control ← freshProofName site.name `control
  let execution ← freshProofName site.name `execution
  let mut facts := #[]
  let mut tactics : Array (TSyntax `tactic) := #[]
  for (binding, index) in site.scope.zipIdx do
    if binding.privatePending then
      let fixed ← freshProofName site.name `pendingFixed
      let sourceVar ← variableTerm index
      facts := facts.push fixed
      tactics := tactics.push (← `(tactic|
        have $fixed:ident : Complexity.Language.Env.get ($finish:ident).locals $sourceVar = none := by
          simpa only [$viewSymmApply:ident, $entry:ident,
            Complexity.Language.Env.cons_here, Complexity.Language.Env.cons_there] using
            Complexity.Language.Exec.get_eq $execution:ident $sourceVar
              (by simp [$preservedArgs,*])))
  let frameArgs ← namedSimpArgs (#[entry, visible, viewApply] ++ facts)
  let mut declarations := #[
    (← `(command|
      /-- The actual guard leaves the private completion slots empty. Only
      the source-visible locals and heap may change before the loop body. -/
      theorem $guardFrame:ident ($start:ident : $visibleType:ident)
          {$heap:ident : Complexity.Language.Heap}
          {$finish:ident : Complexity.Language.State $types}
          {$control:ident : Complexity.Language.Control .bool}
          ($execution:ident : Complexity.Language.Exec $program:ident $guard:ident
            ⟨($view:ident).symm ($entry:ident $start:ident), $heap:ident⟩
            $finish:ident $control:ident) :
          $entry:ident ($visible:ident ($view:ident ($finish:ident).locals)) =
            $view:ident ($finish:ident).locals := by
        $tactics:tactic*
        simp only [$frameArgs,*])).raw]
  let state ← freshProofName site.name `state
  let value ← freshProofName site.name `value
  let stopped ← freshProofName site.name `stopped
  declarations := declarations.push (← `(command|
    /-- Local completion exits through the actual next false-guard step. -/
    theorem $guardCompleted:ident ($state:ident : Complexity.Language.State $types)
        ($value:ident : $targetValue)
        ($stopped:ident : ($pendingAtom : Complexity.Language.Atom $types (.option $targetType)).eval
          ($state:ident).locals = some $value:ident) :
        Complexity.Language.Exec $program:ident $guard:ident $state:ident $state:ident
          (.returned false) := by
      apply Complexity.Language.Stmt.LocalReturn.guard_stopped
      exact $stopped:ident)).raw
  let pre ← freshProofName site.name `pre
  let returned ← freshProofName site.name `returned
  let again ← freshProofName site.name `again
  let output ← freshProofName site.name `output
  let invocation ← tupleApplication site.scope guardAction (← `($entry:ident $start:ident))
  declarations := declarations.push (← `(command|
    /-- The real guard's contract mentions only source-visible inputs and
    outputs. Its compiler-slot frame is supplied by the generated bridge. -/
    abbrev $guardContract:ident
        ($pre:ident : $visibleType:ident → Complexity.Language.Heap → Prop)
        ($returned:ident : $visibleType:ident → Complexity.Language.Heap → Bool →
          $visibleType:ident → Complexity.Language.Heap → Prop) : Prop :=
      Complexity.Language.Stmt.BlockSpec (fun ($start:ident : $visibleType:ident) => $invocation)
        $pre:ident (fun _ _ _ _ => False)
        (fun $start:ident $heap:ident $again:ident $output:ident $finish:ident =>
          $returned:ident $start:ident $heap:ident $again:ident
            ($visible:ident $output:ident) $finish:ident))).raw
  let name := loopMember site "completion_rel_contract"
  let contract := loopMember site "completion_contract"
  let bodyContract := loopMember site "body_completion_contract"
  let body := loopMember site "Body"
  let pending := loopMember site "pending"
  let pendingEval := loopMember site "pending_eval"
  let bodyFrame := loopMember site "body_ancestor_pending_frame"
  let visibleEntry := loopMember site "visible_entry"
  let pendingEntry := loopMember site "pending_entry"
  let reconstruct := loopMember site "reconstruct"
  let reconstructNone := loopMember site "reconstruct_none"
  let modelType ← freshProofName site.name `Model
  let stateRel ← freshProofName site.name `stateRel
  let invariant ← freshProofName site.name `invariant
  let relation ← freshProofName site.name `relation
  let wellFounded ← freshProofName site.name `wellFounded
  let ready ← freshProofName site.name `ready
  let normal ← freshProofName site.name `normal
  let guardSpec ← freshProofName site.name `guardSpec
  let bodySpec ← freshProofName site.name `bodySpec
  let model ← freshProofName site.name `model
  let next ← freshProofName site.name `next
  let valid ← freshProofName site.name `valid
  let represented ← freshProofName site.name `represented
  let property ← freshProofName site.name `property
  let checked ← freshProofName site.name `checked
  declarations := declarations.push (← `(command|
    /-- Relate this actual loop to a mathematical state without private completion
    slots. Only a continuing body supplies another invariant and a decrease;
    a local result exits through the real next guard. -/
    theorem $name:ident {$modelType:ident : Type}
        ($stateRel:ident : $modelType:ident → $visibleType:ident → Complexity.Language.Heap → Prop)
        ($invariant:ident : $modelType:ident → Prop)
        {$relation:ident : $modelType:ident → $modelType:ident → Prop}
        ($wellFounded:ident : WellFounded $relation:ident)
        ($ready:ident : $modelType:ident → $visibleType:ident → Complexity.Language.Heap →
          $visibleType:ident → Complexity.Language.Heap → Prop)
        ($normal:ident : $visibleType:ident → Complexity.Language.Heap → Prop)
        ($returned:ident : $targetValue → $visibleType:ident → Complexity.Language.Heap → Prop)
        ($guardSpec:ident : ∀ $model:ident, $invariant:ident $model:ident →
          $guardContract:ident ($stateRel:ident $model:ident)
            (fun $start:ident $heap:ident $again:ident $output:ident $finish:ident =>
              if $again:ident then
                $ready:ident $model:ident $start:ident $heap:ident $output:ident $finish:ident
              else $normal:ident $output:ident $finish:ident))
        ($bodySpec:ident : ∀ $model:ident $start:ident $heap:ident,
          $invariant:ident $model:ident → $stateRel:ident $model:ident $start:ident $heap:ident →
          $bodyContract:ident ($ready:ident $model:ident $start:ident $heap:ident)
            (fun _ _ $output:ident $finish:ident => ∃ $next:ident,
              $invariant:ident $next:ident ∧
                $stateRel:ident $next:ident $output:ident $finish:ident ∧
                $relation:ident $next:ident $model:ident)
            (fun _ _ => $returned:ident))
        ($model:ident : $modelType:ident) ($valid:ident : $invariant:ident $model:ident) :
        $contract:ident ($stateRel:ident $model:ident)
          (fun _ _ => $normal:ident) (fun _ _ => $returned:ident) := by
      have $checked:ident := Complexity.Language.Stmt.observe_while_visible_completion_contract
        $view:ident $program:ident $guard:ident $body:ident $pendingAtom $guardCompleted:ident
        $visible:ident $entry:ident $reconstruct:ident $visibleEntry:ident
        (fun $start:ident => $pendingEntry:ident $start:ident) $reconstructNone:ident
        (by
          intro $start:ident $heap:ident $output:ident $finish:ident $again:ident $execution:ident
          have $property:ident := $guardFrame:ident $start:ident
            (Complexity.Language.Stmt.observe_eq_some_iff.mp $execution:ident)
          simpa only [Equiv.apply_symm_apply] using $property:ident)
        (by
          intro $start:ident $heap:ident $output:ident $finish:ident $execution:ident
          have $property:ident := $bodyFrame:ident
            (Complexity.Language.Stmt.observe_eq_some_iff.mp $execution:ident)
          simpa only [Equiv.apply_symm_apply, $pendingEval:ident] using $property:ident)
        $stateRel:ident $invariant:ident $wellFounded:ident $ready:ident
        $normal:ident $returned:ident $guardSpec:ident
        (by
          intro $model:ident $start:ident $heap:ident $valid:ident $represented:ident
          refine Complexity.Language.Stmt.BlockSpec.mono
            ($bodySpec:ident $model:ident $start:ident $heap:ident $valid:ident $represented:ident)
            (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible)
          intro _ _ $output:ident $finish:ident _ $property:ident
          cases $stopped:ident : $pending:ident $output:ident <;>
            simpa only [$pendingEval:ident, $stopped:ident] using $property:ident)
        $model:ident $valid:ident
      refine Complexity.Language.Stmt.BlockSpec.mono $checked:ident
        (fun _ _ initial => initial) ?_ (fun _ _ _ _ _ _ impossible => impossible)
      intro _ _ $output:ident $finish:ident _ $property:ident
      cases $stopped:ident : $pending:ident $output:ident <;>
        simpa only [$pendingEval:ident, $stopped:ident] using $property:ident)).raw
  return declarations

end Core

end Complexity.Language.Syntax
