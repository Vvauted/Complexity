/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.LocalReturn
import Complexity.Language.Eval.Locals.Composition
import Complexity.Language.Eval.Locals.Continuation
import Complexity.Language.Eval.Locals.Effects

/-!
# Generated block equations and continuation specifications

Constructs one-step block observation equations and continuation/scratch specifications from
the recorded source proof traces. Lexical transport and named sub-block observations are proof
interfaces for the same actual program, not an alternate evaluator.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def loopEquationDeclarations (site : BlockSite) (sites : Array BlockSite)
    (calleeFolds : Array (TSyntax `ident)) : MacroM (Array Syntax) := do
  let loopCode := loopMember site "Code"
  let nestedSites := sites.filter fun other =>
    other.name.getId != site.name.getId &&
      (site.body.raw.hasIdent (loopMember other "Code").getId ||
        site.guard.any (fun guard => guard.raw.hasIdent (loopMember other "Code").getId))
  let expandedFolds ← nestedSites.mapM fun other => do
    return (other, ← freshProofName other.name `nestedObservation)
  let expandedFoldArgs ← namedSimpArgs (expandedFolds.map (·.2))
  let viewDefinitions ← namedSimpArgs ((#[site] ++ nestedSites).map fun other =>
    loopMember other "View")
  let foldNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "body_observe", loopMember other "observe"] ++
      if other.guard.isSome then #[loopMember other "guard_observe"] else #[])
  let nestedLoops ← namedSimpArgs (sites.map fun other => loopMember other "observe")
  let viewNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "view_apply", loopMember other "view_symm_apply"])
  let calleeFolds ← namedSimpArgs calleeFolds
  let compositionArgs ← constantSimpArgs #[``Complexity.Language.Stmt.observe_skip,
    ``Complexity.Language.Stmt.LocalReturn.store, ``Complexity.Language.Stmt.LocalReturn.resume,
    ``Complexity.Language.Stmt.LocalReturn.guard,
    ``Complexity.Language.Stmt.observe_assign, ``Complexity.Language.Stmt.observe_ret,
    ``Complexity.Language.Stmt.observe_seq, ``Complexity.Language.Stmt.observe_ite,
    ``Complexity.Language.Stmt.observe_matchOption,
    ``Complexity.Language.Stmt.observe_letPrim, ``Complexity.Language.Stmt.observe_read,
    ``Complexity.Language.Stmt.observe_readNode, ``Complexity.Language.Stmt.observe_consNode,
    ``Complexity.Language.Stmt.observe_write, ``Complexity.Language.Stmt.observe_slice,
    ``Complexity.Language.Stmt.observe_alloc, ``Complexity.Language.Stmt.observe_call]
  let sharedArgs := compositionArgs ++ nestedLoops ++ viewNames ++ calleeFolds ++
    (← viewSimpArgs) ++ (← valueSimpArgs)
  let mut declarations := #[]
  let observations := (if site.guard.isSome then [("guard", "Guard")] else []) ++
    [("body", "Body")]
  for (suffix, codeSuffix) in observations do
    let name := loopMember site suffix
    let equation := loopMember site (suffix ++ "_eq")
    let code := loopMember site codeSuffix
    let applied := scopeApplication site.scope name
    let allArgs := (← namedSimpArgs #[code]) ++ sharedArgs
    -- Ordinary blocks normalize through the proved projection equations. Only
    -- actual nested blocks need their composed and named views aligned below.
    let initialProof ← if nestedSites.isEmpty then `(source_conversion% $applied =>
        unfold $name:ident
        simp (config := { implicitDefEqProofs := false }) only [$allArgs,*]
        dsimp only [Complexity.Language.Env.equivProd, Complexity.Language.Env.equivUnit,
          Equiv.symm]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [Equiv.coe_fn_mk, Complexity.Language.Env.cons_here,
            Complexity.Language.Env.cons_there, Complexity.Language.Env.head_cons,
            Complexity.Language.Env.tail_cons, Complexity.Language.Env.get_tail])
    else `(source_conversion% $applied =>
        unfold $name:ident
        simp (config := { implicitDefEqProofs := false }) only [$allArgs,*]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [$viewDefinitions,*]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [$expandedFoldArgs,*]
        dsimp only [Complexity.Language.Env.equivProd, Complexity.Language.Env.equivUnit,
          Equiv.symm]
        simp (config := { failIfUnchanged := false, implicitDefEqProofs := false }) only
          [Equiv.coe_fn_mk, Complexity.Language.Env.cons_here,
            Complexity.Language.Env.cons_there, Complexity.Language.Env.head_cons,
            Complexity.Language.Env.tail_cons, Complexity.Language.Env.get_tail])
    let mut proof := initialProof
    -- Composing lexical bindings constructs a view definitionally equal to a
    -- nested block's named View. Normalize just these equation-local copies;
    -- public views stay opaque to the separate continuation and frame proofs.
    for (other, folded) in expandedFolds.reverse do
      let observed := loopMember other "observe"
      let view := loopMember other "View"
      proof ← `(by
        have $folded:ident := $observed:ident
        dsimp only [$view:ident] at $folded:ident
        exact $proof)
    let curriedProof ← curryScope site.scope proof
    declarations := declarations.push
      (← `(command| source_equation% $equation:ident := $curriedProof)).raw
  let name := site.name
  let equation := loopMember site "eq"
  let applied := scopeApplication site.scope name
  let composition := mkCIdent (if site.guard.isSome then
    ``Complexity.Language.Stmt.observe_while else ``Complexity.Language.Stmt.observe_scope)
  let proof ← curryScope site.scope (← `(source_conversion% $applied =>
      unfold $name:ident
      rw [$loopCode:ident, $composition:ident]
      simp only [$foldNames,*]))
  declarations := declarations.push (← `(command| source_equation% $equation:ident := $proof)).raw
  return declarations

def loopContinuationDeclaration (program : TSyntax `ident) (site : BlockSite)
    (sites : Array BlockSite) : MacroM Syntax := do
  let name := loopMember site "continue_eq"
  let view := loopMember site "View"
  let code := loopMember site "Code"
  let types ← scopeTypes site.scope
  let result ← valueTypeTerm site.result
  let entry ← freshProofName site.name `entry
  let next ← freshProofName site.name `next
  let control ← freshProofName site.name `control
  let locals ← freshProofName site.name `locals
  let value ← freshProofName site.name `value
  let error ← freshProofName site.name `error
  let execution ← freshProofName site.name `execution
  let initialHeap ← freshProofName site.name `initialHeap
  let finalHeap ← freshProofName site.name `finalHeap
  let input ← `($view:ident $entry:ident)
  let invocation ← tupleApplication site.scope site.name input
  let fields ← tupleFields site.scope ⟨locals.raw⟩
  let mut restored ← `(Complexity.Language.Env.empty)
  let mut captures : Array (TSyntax `ident × TSyntax `term) := #[]
  for (binding, index) in site.scope.zipIdx.reverse do
    let sourceVar ← variableTerm index
    let field ← if binding.isMutable then pure fields[index]! else
      `(Complexity.Language.Env.get $entry:ident $sourceVar)
    let type ← typeTerm binding.type
    restored ← `(Complexity.Language.Env.cons (τ := $type) $field $restored)
    unless binding.isMutable do
      captures := captures.push (← freshProofName site.name `capture, sourceVar)
  let captureNames ← namedSimpArgs (captures.map (·.1))
  let viewNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "view_apply", loopMember other "view_symm_apply"])
  let codeNames ← namedSimpArgs (sites.flatMap fun other =>
    #[loopMember other "Code", loopMember other "Body"] ++
      if other.guard.isSome then #[loopMember other "Guard"] else #[])
  let viewArgs := viewNames ++ (← viewSimpArgs)
  let normalArgs := viewArgs ++ captureNames
  let preservedArgs := codeNames ++
    (← constantSimpArgs #[``Complexity.Language.Stmt.PreservesLocal,
      ``Complexity.Language.Var.index, ``Complexity.Language.Stmt.LocalReturn.store,
      ``Complexity.Language.Stmt.LocalReturn.resume, ``Complexity.Language.Stmt.LocalReturn.guard])
  let captureArgs := (← constantSimpArgs #[``Equiv.symm_apply_apply]) ++ viewArgs ++
    (← constantSimpArgs #[``Complexity.Language.Env.cons_here, ``Complexity.Language.Env.cons_there])
  let mut normalProof ← `(by
    simp only [$normalArgs,*])
  for (capture, sourceVar) in captures.reverse do
    normalProof ← `(by
      have $capture:ident := Complexity.Language.Exec.get_eq $execution:ident $sourceVar
        (by simp [$preservedArgs,*])
      simp only [$captureArgs,*] at $capture:ident
      exact $normalProof)
  let declaration ← `(command|
    /-- Resume from actual mutable locals; immutable captures are preserved by the source frame. -/
    theorem $name:ident ($entry:ident : Complexity.Language.Env $types)
        ($next:ident : Complexity.Language.Env $types →
          ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part) $result) :
        Complexity.Language.Stmt.evalWith $code:ident $program:ident $entry:ident $next:ident = (do
          let ($control:ident, $locals:ident) ← MonadLift.monadLift $invocation
          match $control:ident with
          | .normal => $next:ident $restored
          | .returned $value:ident => pure $value:ident
          | .fault $error:ident => throw $error:ident) := by
      rw [Complexity.Language.Stmt.evalWith_eq_observe $view:ident]
      apply Complexity.Language.Stmt.observe_bind_congr_except
        $view:ident $code:ident $program:ident ($view:ident $entry:ident)
      intro $initialHeap:ident $finalHeap:ident $control:ident $locals:ident $execution:ident
      cases $control:ident with
      | normal => exact $normalProof
      | returned value => rfl
      | fault error => rfl)
  return declaration.raw

def scopeSpecificationDeclaration (program : TSyntax `ident) (site : BlockSite) :
    MacroM Syntax := do
  let name := loopMember site "spec"
  let localsType := loopMember site "Locals"
  let view := loopMember site "View"
  let body := loopMember site "Body"
  let result ← typeTerm site.result
  let tuple ← scopeTuple site.scope
  let invocation := scopeApplication site.scope site.name
  let bodyInvocation := scopeApplication site.scope (loopMember site "body")
  let post ← freshProofName site.name `post
  let heap ← freshProofName site.name `heap
  let outcome ← freshProofName site.name `outcome
  let finish ← freshProofName site.name `finish
  let postType ← `(Std.Do.PostCond (Complexity.Language.Control $result × $localsType:ident)
    (.arg Complexity.Language.Heap .pure))
  let type ← quantifyScope site.scope (← `(∀ ($post:ident : $postType),
    Std.Do.Triple (m := StateT Complexity.Language.Heap Part)
      (ps := .arg Complexity.Language.Heap .pure) $invocation
      (fun $heap:ident =>
        ((Std.Do.WP.wp $bodyInvocation).apply
          (fun $outcome:ident $finish:ident => ⟨
            Complexity.Language.ScopeSafe $heap:ident
              ⟨($view:ident).symm ($outcome:ident).2, $finish:ident⟩ ($outcome:ident).1 ∧
            (($post:ident).1 $outcome:ident
              (Complexity.Language.Heap.take $finish:ident ($heap:ident).objects.size)).down⟩,
            ⟨⟩)) $heap:ident) $post:ident))
  let proof ← curryScope site.scope (← `(fun $post:ident =>
    Complexity.Language.Stmt.observe_scope_safe_spec $view:ident $program:ident
      $body:ident $tuple $post:ident))
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Compose the actual body specification with safe scratch release. Surviving
    locals and return values stay rooted; current retained contents are not rolled back. -/
    theorem $name:ident : $type := $proof)).raw

end Core

end Complexity.Language.Syntax
