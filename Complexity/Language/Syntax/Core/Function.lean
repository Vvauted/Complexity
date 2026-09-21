/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.LocalReturn
import Complexity.Language.Linking.Eval
import Complexity.Language.Linking.Extension
import Complexity.Language.Eval.Continuation

/-!
# Generated source function observations and import bridges

Constructs function observations, equations, ordinary-parameter total contracts, specifications
and checked import declarations. The source table and its emission order are assembled separately
in `Core.Emission`.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def observationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let mut arguments ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let type ← typeTerm param.type
    let parameter := param.name
    arguments ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $arguments)
  let result ← valueTypeTerm fn.result
  let mut type ← `(ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result)
  let mut value ← `(Complexity.Language.Program.eval $programName:ident $id:ident $arguments)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    value ← `(fun ($parameter:ident : $parameterType) => $value)
  let declaration ← `(command|
    /-- The named function's actual partial source action, with ordinary typed arguments
    and an explicitly supplied shared heap. -/
    noncomputable def $name:ident : $type := $value)
  return declaration.raw

def calleeObservationDeclaration (family program : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name "_observe"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let env ← freshProofName fn.name `arguments
  let mut remaining ← `($env:ident)
  let mut values := #[]
  for _ in fn.params do
    values := values.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let applied := Lean.Syntax.mkApp ⟨observation.raw⟩ values
  let type ← `(∀ ($env:ident : Complexity.Language.Env $params),
    Complexity.Language.Program.eval $program:ident $id:ident $env:ident = $applied)
  let mut proof ← `((Complexity.Language.Env.forall_nil _).mpr (by rfl))
  for (param, index) in fn.params.zipIdx.reverse do
    let sourceType ← typeTerm param.type
    let valueType ← valueTypeTerm param.type
    let rest ← parameterTypes (fn.params.extract (index + 1) fn.params.size)
    proof ← `((Complexity.Language.Env.forall_cons (τ := $sourceType) (Γ := $rest) _).mpr
      (fun ($(param.name):ident : $valueType) => $proof))
  return (← `(command|
    /-- Fold an actual source invocation back to its named ordinary-argument observation. -/
    theorem $name:ident : $type := $proof)).raw

def equationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (lowered : LoweredBlock)
    (importFolds : Array (TSyntax `ident)) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name (if pureMode then "_action_eq" else "_eq")
  let observation := actionName family fn.name pureMode
  let bodyName := generatedName family fn.name "Body"
  let id := generatedName family fn.name "Id"
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let lhs := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let fallthrough ← `(doElem| throw Complexity.Language.Fault.missingReturn)
  let body := lowered.proofSequence fallthrough
  let result ← valueTypeTerm fn.result
  let loopContinuations ← namedSimpArgs (lowered.sites.map fun site => loopMember site "continue_eq")
  let loopViews ← namedSimpArgs (lowered.sites.flatMap fun site =>
    #[loopMember site "view_apply", loopMember site "view_symm_apply"])
  let compositionArgs ← constantSimpArgs #[``Complexity.Language.Stmt.evalWith_skip,
    ``Complexity.Language.Stmt.LocalReturn.store, ``Complexity.Language.Stmt.LocalReturn.resume,
    ``Complexity.Language.Stmt.LocalReturn.guard,
    ``Complexity.Language.Stmt.evalWith_ret, ``Complexity.Language.Stmt.evalWith_assign,
    ``Complexity.Language.Stmt.evalWith_letPrim, ``Complexity.Language.Stmt.evalWith_seq,
    ``Complexity.Language.Stmt.evalWith_ite, ``Complexity.Language.Stmt.evalWith_matchOption,
    ``Complexity.Language.Stmt.evalWith_call,
    ``Complexity.Language.Stmt.evalWith_read, ``Complexity.Language.Stmt.evalWith_write,
    ``Complexity.Language.Stmt.evalWith_readNode, ``Complexity.Language.Stmt.evalWith_consNode,
    ``Complexity.Language.Stmt.evalWith_slice, ``Complexity.Language.Stmt.evalWith_alloc]
  let allArgs := (← namedSimpArgs (#[bodyName] ++ importFolds)) ++ loopContinuations ++ loopViews ++
    (← viewSimpArgs) ++ compositionArgs ++ (← valueSimpArgs) ++
    (← constantSimpArgs #[``Complexity.Language.Env.tail_set_here,
      ``Complexity.Language.Env.tail_set_there, ``ExceptT.bind_throw])
  let mut type ← `($lhs = ((do $body:doSeq) : ExceptT Complexity.Language.Fault
    (StateT Complexity.Language.Heap Part) $result))
  let mut proof ← `(by
    have body_selected : ($programName:ident).body $id:ident = $bodyName:ident := rfl
    conv =>
      lhs
      unfold $observation:ident
      rw [Complexity.Language.Program.eval_eq_evalWith, body_selected]
    simp only [$allArgs,*]
    -- The semantic and native Option eliminators can have different motives.
    -- Compare actual bind results and branches without unfolding any callee.
    all_goals repeat' first
      | rfl
      | (split <;> simp_all only [Option.some.injEq, reduceCtorEq])
      | (apply bind_congr; intro value)
      | (apply congrFun; apply bind_congr; intro value)
      | (congr 1; funext value)
    all_goals rfl)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  let declaration ← `(command|
    /-- One source-body equation in ordinary monadic notation; named callees remain opaque. -/
    theorem $name:ident : $type := $proof)
  return declaration.raw

def argumentsDeclaration (family : TSyntax `ident) (fn : Function) : MacroM Syntax := do
  let name := generatedName family fn.name "_args"
  let params ← parameterTypes fn.params
  let mut type ← `(Complexity.Language.Env $params)
  let mut value ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let sourceType ← typeTerm param.type
    value ← `(Complexity.Language.Env.cons (τ := $sourceType) $parameter:ident $value)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    value ← `(fun ($parameter:ident : $parameterType) => $value)
  return (← `(command|
    /-- The actual declared argument environment, constructed from ordinary source parameters.
    This is proof-side parameter transport, not an additional runtime operation. -/
    abbrev $name:ident : $type := $value)).raw

def totalDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM (Array Syntax) := do
  let name := generatedName family fn.name "_total_iff"
  let contractName := generatedName family fn.name "_contract"
  let onArgsName := generatedName family fn.name "_onArgs"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let pre := mkIdent (← Macro.addMacroScope `pre)
  let post := mkIdent (← Macro.addMacroScope `post)
  let env := mkIdent (← Macro.addMacroScope `env)
  let initialHeap := mkIdent (← Macro.addMacroScope `initialHeap)
  let value := mkIdent (← Macro.addMacroScope `value)
  let finalHeap := mkIdent (← Macro.addMacroScope `finalHeap)
  let result ← valueTypeTerm fn.result
  let mut preType ← `(Complexity.Language.Heap → Prop)
  let mut postType ← `(Complexity.Language.Heap → $result → Complexity.Language.Heap → Prop)
  for param in fn.params.reverse do
    let type ← valueTypeTerm param.type
    preType ← `($type → $preType)
    postType ← `($type → $postType)
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let mut envArguments : Array (TSyntax `term) := #[]
  let mut remaining ← `($env:ident)
  for _ in fn.params do
    envArguments := envArguments.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let codomain := mkIdent (← Macro.addMacroScope `α)
  let function := mkIdent (← Macro.addMacroScope `function)
  let mut functionType : TSyntax `term := ⟨codomain.raw⟩
  for param in fn.params.reverse do
    let type ← valueTypeTerm param.type
    functionType ← `($type → $functionType)
  let applied := Lean.Syntax.mkApp ⟨function.raw⟩ envArguments
  let params ← parameterTypes fn.params
  let onArgsDeclaration ← `(command|
    /-- Apply a predicate, postcondition or bound with ordinary source parameters
    to the actual argument environment. No new contract or execution is introduced. -/
    abbrev $onArgsName:ident {$codomain:ident : Sort _}
        ($function:ident : $functionType) ($env:ident : Complexity.Language.Env $params) :
        $codomain:ident := $applied)
  let ordinaryPre := Lean.Syntax.mkApp ⟨pre.raw⟩ (arguments.push ⟨initialHeap.raw⟩)
  let ordinaryPost := Lean.Syntax.mkApp ⟨post.raw⟩
    (arguments ++ #[⟨initialHeap.raw⟩, ⟨value.raw⟩, ⟨finalHeap.raw⟩])
  let invocation := Lean.Syntax.mkApp ⟨observation.raw⟩ (arguments.push ⟨initialHeap.raw⟩)
  let mut ordinary ← `(∀ ($initialHeap:ident : Complexity.Language.Heap),
    $ordinaryPre → ∃ ($value:ident : $result) ($finalHeap:ident : Complexity.Language.Heap),
      $invocation = Part.some (.ok $value:ident, $finalHeap:ident) ∧ $ordinaryPost)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    ordinary ← `(∀ ($parameter:ident : $type), $ordinary)
  let hypothesis := mkIdent (← Macro.addMacroScope `specification)
  let mut encodedArgs ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← typeTerm param.type
    encodedArgs ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $encodedArgs)
  let mut forward ← `($hypothesis:ident $encodedArgs)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    forward ← `(fun ($parameter:ident : $type) => $forward)
  forward ← `(fun $hypothesis:ident => $forward)
  let mut backward := Lean.Syntax.mkApp ⟨hypothesis.raw⟩ arguments
  backward ← `((Complexity.Language.Env.forall_nil _).mpr $backward)
  for (param, index) in fn.params.zipIdx.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    let sourceType ← typeTerm param.type
    let remainingTypes ← parameterTypes (fn.params.extract (index + 1) fn.params.size)
    backward ← `((Complexity.Language.Env.forall_cons (τ := $sourceType)
      (Γ := $remainingTypes) _).mpr (fun ($parameter:ident : $type) => $backward))
  backward ← `(fun $hypothesis:ident => $backward)
  let contractDeclaration ← `(command|
    /-- Budget-free total correctness with ordinary source parameters and relational
    initial/final heap postconditions. This is the existing source function contract. -/
    abbrev $contractName:ident ($pre:ident : $preType) ($post:ident : $postType) : Prop :=
      Complexity.Language.FunctionTotal $programName:ident $id:ident
        ($onArgsName:ident $pre:ident) ($onArgsName:ident $post:ident))
  let declaration ← `(command|
    /-- The source contract is equivalent to ordinary curried preconditions and
    successful result/heap postconditions, including termination and absence of faults. -/
    theorem $name:ident ($pre:ident : $preType) ($post:ident : $postType) :
        $contractName:ident $pre:ident $post:ident ↔ $ordinary := by
      rw [$contractName:ident, Complexity.Language.FunctionTotal.iff_eval]
      exact ⟨$forward, $backward⟩)
  let tripleName := generatedName family fn.name "_contract_iff_triple"
  let currentHeap := mkIdent (← Macro.addMacroScope `currentHeap)
  let action := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let mut triple ← `(∀ ($initialHeap:ident : Complexity.Language.Heap),
    Std.Do.Triple (m := ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part))
      (ps := .except Complexity.Language.Fault (.arg Complexity.Language.Heap .pure))
      $action
      (fun $currentHeap:ident => ⟨$currentHeap:ident = $initialHeap:ident ∧ $ordinaryPre⟩)
      (fun $value:ident $finalHeap:ident => ⟨$ordinaryPost⟩,
        (fun _ _ => ⟨False⟩, ⟨⟩)))
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← valueTypeTerm param.type
    triple ← `(∀ ($parameter:ident : $type), $triple)
  let tripleDeclaration ← `(command|
    open scoped Part.TotalCorrectness in
    /-- Prove the ordinary-parameter source contract with a total-correctness triple
    for the same action. The ghost initial heap equals the actual entry heap;
    successful results use the actual final heap, and faults are excluded. -/
    theorem $tripleName:ident ($pre:ident : $preType) ($post:ident : $postType) :
        $contractName:ident $pre:ident $post:ident ↔ $triple := by
      rw [$contractName:ident, Complexity.Language.FunctionTotal.iff_triple_eval]
      exact ⟨$forward, $backward⟩)
  return #[onArgsDeclaration.raw, contractDeclaration.raw, declaration.raw, tripleDeclaration.raw]

def specificationDeclaration (family programName : TSyntax `ident)
    (fn : Function) (pureMode : Bool) : MacroM Syntax := do
  let name := generatedName family fn.name "_spec"
  let observation := actionName family fn.name pureMode
  let id := generatedName family fn.name "Id"
  let params ← parameterTypes fn.params
  let result ← valueTypeTerm fn.result
  let pre := mkIdent (← Macro.addMacroScope `pre)
  let post := mkIdent (← Macro.addMacroScope `post)
  let contract := mkIdent (← Macro.addMacroScope `contract)
  let continuation := mkIdent (← Macro.addMacroScope `continuation)
  let initialHeap := mkIdent (← Macro.addMacroScope `initialHeap)
  let value := mkIdent (← Macro.addMacroScope `value)
  let finalHeap := mkIdent (← Macro.addMacroScope `finalHeap)
  let arguments : Array (TSyntax `term) := fn.params.map fun param => ⟨param.name.raw⟩
  let invocation := Lean.Syntax.mkApp ⟨observation.raw⟩ arguments
  let mut encodedArgs ← `(Complexity.Language.Env.empty)
  for param in fn.params.reverse do
    let parameter := param.name
    let type ← typeTerm param.type
    encodedArgs ← `(Complexity.Language.Env.cons (τ := $type) $parameter:ident $encodedArgs)
  let mut type ← `(∀ ($continuation:ident : Std.Do.PostCond $result
      (.except Complexity.Language.Fault (.arg Complexity.Language.Heap .pure))),
    Std.Do.Triple (m := ExceptT Complexity.Language.Fault (StateT Complexity.Language.Heap Part))
      (ps := .except Complexity.Language.Fault (.arg Complexity.Language.Heap .pure))
      $invocation
      (fun $initialHeap:ident => ⟨$pre:ident $encodedArgs $initialHeap:ident ∧
        ∀ $value:ident $finalHeap:ident,
          $post:ident $encodedArgs $initialHeap:ident $value:ident $finalHeap:ident →
            (($continuation:ident).1 $value:ident $finalHeap:ident).down⟩)
      $continuation:ident)
  let mut proof ← `(fun $continuation:ident =>
    Complexity.Language.FunctionTotal.triple_spec $contract:ident $encodedArgs $continuation:ident)
  for param in fn.params.reverse do
    let parameter := param.name
    let parameterType ← valueTypeTerm param.type
    type ← `(∀ ($parameter:ident : $parameterType), $type)
    proof ← `(fun ($parameter:ident : $parameterType) => $proof)
  return (← `(command|
    open scoped Part.TotalCorrectness in
    /-- Apply a supplied source contract with ordinary named arguments and its
    actual returned value and final heap. No callee body or new contract is inferred. -/
    theorem $name:ident
        {$pre:ident : Complexity.Language.Env $params → Complexity.Language.Heap → Prop}
        {$post:ident : Complexity.Language.Env $params → Complexity.Language.Heap →
          $result → Complexity.Language.Heap → Prop}
        ($contract:ident : Complexity.Language.FunctionTotal $programName:ident $id:ident
          $pre:ident $post:ident) : $type := $proof)).raw

def importedDeclarations (family : TSyntax `ident)
    (imports : Array ImportedProgram) : MacroM (Option ImportDeclarations) := do
  let some first := imports[0]? | return none
  let mut program : TSyntax `term := ⟨(mkCIdent (first.family ++ `program)).raw⟩
  let mut signatures : TSyntax `term := ⟨(mkCIdent (first.family ++ `signatures)).raw⟩
  let mut embeddings : Array ImportEmbedding := #[⟨first,
    ← `(Complexity.Language.SignatureMap.refl $signatures),
    ← `(Complexity.Language.Program.Embeds.refl $program)⟩]
  for imported in imports.toList.drop 1 do
    let next : TSyntax `term := ⟨(mkCIdent (imported.family ++ `program)).raw⟩
    let nextSignatures : TSyntax `term := ⟨(mkCIdent (imported.family ++ `signatures)).raw⟩
    let leftMap ← `(Complexity.Language.SignatureMap.appendLeft $signatures $nextSignatures)
    let leftProof ← `(Complexity.Language.Program.embeds_link_left $program $next)
    embeddings ← embeddings.mapM fun entry => do
      return { entry with
        map := ← `(Complexity.Language.SignatureMap.trans $(entry.map) $leftMap)
        proof := ← `(Complexity.Language.Program.Embeds.trans $(entry.proof) $leftProof) }
    embeddings := embeddings.push ⟨imported,
      ← `(Complexity.Language.SignatureMap.appendRight $signatures $nextSignatures),
      ← `(Complexity.Language.Program.embeds_link_right $program $next)⟩
    program ← `(Complexity.Language.Program.link $program $next)
    signatures ← `($signatures ++ $nextSignatures)
  let signaturesName := mkIdentFrom family (family.getId ++ `importedSignatures)
  let programName := mkIdentFrom family (family.getId ++ `importedProgram)
  let signatureDeclaration ← `(command|
    /-- The complete signature tables retained from imported source programs. -/
    abbrev $signaturesName:ident : List Complexity.Language.Signature := $signatures)
  let programDeclaration ← `(command|
    /-- Actual imported function bodies with their internal calls relocated. -/
    def $programName:ident : Complexity.Language.Program $signaturesName:ident := $program)
  return some ⟨#[signatureDeclaration.raw, programDeclaration.raw],
    ⟨programName.raw⟩, ⟨signaturesName.raw⟩, embeddings⟩

def importedObservationDeclaration (program map embedded : TSyntax `ident)
    (source : ImportedProgram) (fn : FunctionInfo) (callee : Callee) : MacroM Syntax := do
  let params ← parameterTypes callee.params
  let env ← freshProofName callee.name `arguments
  let originalId := mkCIdent ((source.family ++ fn.name).appendAfter "Id")
  let originalFold := mkCIdent ((source.family ++ fn.name).appendAfter "_observe")
  let mut remaining ← `($env:ident)
  let mut arguments := #[]
  for _ in callee.params do
    arguments := arguments.push (← `(Complexity.Language.Env.head $remaining))
    remaining ← `(Complexity.Language.Env.tail $remaining)
  let observed := Lean.Syntax.mkApp ⟨callee.observation.raw⟩ arguments
  return (← `(command|
    /-- Reuse an imported native action through the proved embedding of its real body. -/
    theorem $(callee.fold):ident ($env:ident : Complexity.Language.Env $params) :
        Complexity.Language.Program.eval $program:ident $(callee.id):ident $env:ident =
          $observed := by
      change Complexity.Language.SignatureMap.eval $map:ident $program:ident
        $originalId:ident $env:ident = _
      rw [Complexity.Language.Program.Embeds.eval_eq $embedded:ident]
      exact $originalFold:ident $env:ident)).raw

end Core

end Complexity.Language.Syntax
