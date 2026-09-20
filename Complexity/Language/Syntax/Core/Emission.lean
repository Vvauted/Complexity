/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core.Statement
import Complexity.Language.Syntax.Core.Completion
import Complexity.Language.Syntax.Core.Contract
import Complexity.Language.Syntax.Core.Observation
import Complexity.Language.Syntax.Core.Function
import Complexity.Language.Syntax.Core.Range
import Complexity.Language.Syntax.Core.Correspondence

/-!
# Ordered assembly of source program declarations

Assembles source signatures, function identities, actual bodies, observations and optional pure
views in their dependency order. Individual builders return syntax; this module alone fixes the
sequence passed to command elaboration and returns metadata for checked registration.
-/

namespace Complexity.Language.Syntax

open Lean
open Lean.Parser.Term

namespace Core

def programDeclarations (family : TSyntax `ident)
    (sources : Array (TSyntax `sourceFunction)) (imports : Array ImportedProgram)
    (pureMode : Bool) (nativeViews : Array NativeView := #[]) :
    MacroM (Syntax × Array FunctionInfo × Array LoopCoordinateRegistration ×
      ActualBlockSites) := do
  let mut functions : Array Function := #[]
  for source in sources do
    let fn ← parseFunction source
    let fn := { fn with nativeView := nativeViews.find? (fun view => view.header.name.getId == fn.name.getId) }
    if functions.any (fun previous => previous.name.getId == fn.name.getId) then
      Macro.throwErrorAt fn.name "duplicate source function name"
    if pureMode then
      unless pureValueType fn.result && fn.params.all (pureValueType ·.type) do
        Macro.throwErrorAt fn.name
          "pure source functions support Nat, Bool, Unit and their products/options, but no nested buffers or node references"
    functions := functions.push fn
  let signaturesName := mkIdentFrom family (family.getId ++ `signatures)
  let localSignaturesName := mkIdentFrom family (family.getId ++ `localSignatures)
  let localBodiesName := mkIdentFrom family (family.getId ++ `localBodies)
  let programName := mkIdentFrom family (family.getId ++ `program)
  let signatures ← functions.mapM fun fn => do
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    `(({ params := $params, result := $result } : Complexity.Language.Signature))
  let imported ← importedDeclarations family imports
  let mut declarations := imported.map (·.declarations) |>.getD #[]
  let signatureValue ← match imported with
    | none => `([$signatures,*])
    | some imported => do
        declarations := declarations.push (← `(command|
          /-- Signatures of the functions added by this source declaration. -/
          abbrev $localSignaturesName:ident : List Complexity.Language.Signature :=
            [$signatures,*])).raw
        `($localSignaturesName:ident ++ $(imported.signatures))
  let signatureDeclaration ← `(command|
    /-- The source program's declared first-order signatures. -/
    abbrev $signaturesName:ident : List Complexity.Language.Signature := $signatureValue)
  declarations := declarations.push signatureDeclaration.raw
  for (fn, index) in functions.zipIdx do
    let id := generatedName family fn.name "Id"
    let number := Syntax.mkNumLit (toString index)
    let declaration ← `(command|
      /-- This named source function's index in its declared signature table. -/
      abbrev $id:ident : Fin ($signaturesName:ident).length := ⟨$number:num, by decide⟩)
    declarations := declarations.push declaration.raw
  let mut callees : Array Callee := functions.map fun fn =>
    { name := fn.name, params := fn.params, result := fn.result
      id := generatedName family fn.name "Id"
      observation := actionName family fn.name pureMode
      fold := generatedName family fn.name "_observe"
      native := if pureMode then some (generatedName family fn.name "") else none
      pureEquation := if pureMode then some (generatedName family fn.name
        (if fn.nativeView.isSome then "_action_eq_pure_raw" else "_action_eq_pure")) else none }
  let mut importedProofs : Array Syntax := #[]
  let mut importedObservations : Array Syntax := #[]
  let mut importFolds : Array (TSyntax `ident) := #[]
  if let some imported := imported then
    for entry in imported.embeddings do
      let importNamespace := family.getId ++ `imports ++ entry.source.name.getId
      let map := mkIdentFrom entry.source.name (importNamespace ++ `map)
      let embedded := mkIdentFrom entry.source.name (importNamespace ++ `embedding)
      let sourceSignatures := mkCIdent (entry.source.family ++ `signatures)
      let sourceProgram := mkCIdent (entry.source.family ++ `program)
      declarations := declarations.push (← `(command|
        /-- Signature-preserving positions of this imported source program. -/
        abbrev $map:ident : Complexity.Language.SignatureMap
            $sourceSignatures:ident $signaturesName:ident :=
          Complexity.Language.SignatureMap.trans $(entry.map)
            (Complexity.Language.SignatureMap.appendRight
              $localSignaturesName:ident $(imported.signatures)))).raw
      importedProofs := importedProofs.push (← `(command|
        /-- The imported functions retain their actual relocated bodies. -/
        theorem $embedded:ident : Complexity.Language.Program.Embeds
            $sourceProgram:ident $map:ident $programName:ident :=
          Complexity.Language.Program.Embeds.trans $(entry.proof)
            (Complexity.Language.Program.embeds_extend $(imported.program)
              $localSignaturesName:ident $localBodiesName:ident))).raw
      for fn in entry.source.functions do
        let name := mkIdentFrom entry.source.name (entry.source.name.getId ++ fn.name)
        if callees.any (fun previous => previous.name.getId == name.getId) then
          Macro.throwErrorAt name "ambiguous source function name"
        let id ← freshProofName family `sourceImportedFunction
        let fold ← freshProofName family `sourceImportedObservation
        let originalId := mkCIdent ((entry.source.family ++ fn.name).appendAfter "Id")
        declarations := declarations.push (← `(command|
          /-- The actual target index of an imported function. -/
          abbrev $id:ident : Fin ($signaturesName:ident).length :=
            Complexity.Language.SignatureMap.toFun $map:ident $originalId:ident)).raw
        let callee : Callee := {
          name
          params := fn.params.map (fun param => ⟨mkIdentFrom entry.source.name param.1, param.2⟩)
          result := fn.result, id, fold
          observation := mkCIdent ((fn.source?.map (·.action)).getD
            ((entry.source.family ++ fn.name).appendAfter (if fn.pure then "_action" else "")))
          native := if fn.pure then some (mkCIdent (entry.source.family ++ fn.name)) else none
          pureEquation := if fn.pure then some (mkCIdent ((entry.source.family ++ fn.name).appendAfter
            (if fn.nativeHeader.isSome then "_action_eq_pure_raw" else "_action_eq_pure"))) else none
          sourceName := some (entry.source.family ++ fn.name) }
        callees := callees.push callee
        importFolds := importFolds.push fold
        importedObservations := importedObservations.push (← importedObservationDeclaration
          programName map embedded entry.source fn callee)
  let mut loweredBodies : Array LoweredBlock := #[]
  for fn in functions do
    let name := generatedName family fn.name "Body"
    let params ← parameterTypes fn.params
    let result ← typeTerm fn.result
    let body ← functionCode family callees fn
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.alloc then
      Macro.throwErrorAt fn.name
        "buffer allocation is effectful and is not supported by 'source_program (pure)'"
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.readNode then
      Macro.throwErrorAt fn.name
        "node reading is effectful and is not supported by 'source_program (pure)'"
    if pureMode && body.term.raw.hasIdent ``Complexity.Language.Stmt.consNode then
      Macro.throwErrorAt fn.name
        "node construction is effectful and is not supported by 'source_program (pure)'"
    if pureMode then
      if body.sites.any (fun site => site.guard.isNone) then
        Macro.throwErrorAt fn.name
          "scratch allocation scopes are effectful and are not supported by 'source_program (pure)'"
      if body.sites.any (fun site => !site.hasStandardRange) then
        Macro.throwErrorAt fn.name
          "pure source loops require standard finite ranges; unbounded while and local-return ranges use source contracts"
      if body.fallsThrough then
        Macro.throwErrorAt fn.name "every pure source function path must return a value"
    loweredBodies := loweredBodies.push body
    for site in body.sites do
      declarations := declarations ++ (← loopCodeDeclarations signaturesName site)
    let declaration ← `(command|
      /-- The named function's actual independently interpreted source body. -/
      def $name:ident : Complexity.Language.Stmt $signaturesName:ident $params $result := $(body.term))
    declarations := declarations.push declaration.raw
  let mut bodies ← `(fun index => Fin.elim0 index)
  for fn in functions.reverse do
    let name := generatedName family fn.name "Body"
    bodies ← `(Fin.cases $name:ident $bodies)
  let programValue ← match imported with
    | none => `(({ body := $bodies } : Complexity.Language.Program $signaturesName:ident))
    | some imported => do
        declarations := declarations.push (← `(command|
          /-- Added function bodies already typed against the complete linked table. -/
          def $localBodiesName:ident : (fn : Fin ($localSignaturesName:ident).length) →
              Complexity.Language.Stmt $signaturesName:ident
                ($localSignaturesName:ident)[fn].params ($localSignaturesName:ident)[fn].result :=
            $bodies)).raw
        `(Complexity.Language.Program.extend $(imported.program)
          $localSignaturesName:ident $localBodiesName:ident)
  let programDeclaration ← `(command|
    /-- The finite table of actual named source bodies. -/
    def $programName:ident : Complexity.Language.Program $signaturesName:ident := $programValue)
  declarations := declarations.push programDeclaration.raw
  declarations := declarations ++ importedProofs ++ importedObservations
  for fn in functions do
    declarations := declarations.push (← argumentsDeclaration family fn)
  for fn in functions do
    declarations := declarations.push (← observationDeclaration family programName fn pureMode)
  for fn in functions do
    declarations := declarations.push (← calleeObservationDeclaration family programName fn pureMode)
  let calleeFolds := callees.map (·.fold)
  let loopSites := loweredBodies.flatMap (·.sites)
  for site in loopSites do
    declarations := declarations ++ (← loopObservationDeclarations programName site)
    declarations := declarations ++ (← completionDeclarations programName site loopSites)
    declarations := declarations ++ (← loopCompletionDeclarations programName site loopSites)
    if site.guard.isSome then
      declarations := declarations ++ (← loopCaptureDeclarations site)
      declarations := declarations ++ (← loopNativeCaptureDeclarations site)
  for site in loopSites do
    declarations := declarations ++ (← loopEquationDeclarations site loopSites calleeFolds)
    declarations := declarations.push (← loopContinuationDeclaration programName site loopSites)
    if site.guard.isSome then
      declarations := declarations ++ (← loopCaptureFrameDeclarations programName site loopSites)
      declarations := declarations ++ (← loopContractDeclarations programName site)
      declarations := declarations ++ (← loopNativeContractDeclarations programName site)
      declarations := declarations.push (← loopIndependentContractDeclaration programName site false)
      declarations := declarations.push (← loopIndependentContractDeclaration programName site true)
      declarations := declarations.push (← loopCountFrameContractDeclaration programName site)
      declarations := declarations.push (← loopRelatedContractDeclaration programName site)
      declarations := declarations.push (← loopTerminationDeclaration programName site false)
      declarations := declarations.push (← loopTerminationDeclaration programName site true)
    else
      declarations := declarations.push (← scopeSpecificationDeclaration programName site)
  for fn in functions, body in loweredBodies do
    declarations := declarations.push
      (← equationDeclaration family programName fn body importFolds pureMode)
  for fn in functions do
    declarations := declarations ++ (← totalDeclaration family programName fn pureMode)
    declarations := declarations.push (← specificationDeclaration family programName fn pureMode)
  if pureMode then
    let order ← pureFunctionOrder family functions loweredBodies
    for (fn, body) in order do
      declarations := declarations.push
        (← nativeDeclaration family fn callees body)
      for site in body.sites.filter (·.hasStandardRange) do
        declarations := declarations.push
          (← rangeCorrespondenceDeclarations programName callees body.sites site
            (fn.nativeView.map (·.simplifications) |>.getD #[]))
      declarations := declarations.push
        (← pureCorrespondenceDeclaration family fn callees body)
      match fn.nativeView with
      | none => declarations := declarations.push (← pureTotalDeclaration family programName fn)
      | some view =>
          declarations := declarations.push (← pureRawCorrespondenceDeclaration family fn view)
          declarations := declarations.push (← pureTotalDeclaration family programName fn)
          declarations := declarations ++ (← nativeRefinementDeclarations family programName fn view)
  let mut coordinates : Array LoopCoordinateRegistration := #[]
  let mut ranges : Array ActualRangeSite := #[]
  let mut whiles : Array ActualWhileSite := #[]
  for site in loopSites do
    if let some request := site.rangeRequest then
      let some range := site.finiteRange
        | Macro.throwErrorAt site.name "a source range tag must identify a finite range"
      let some cursorSlot := site.scope.findIdx? fun binding =>
          binding.proofName.getId == range.cursor.getId
        | Macro.throwErrorAt site.name "the finite range cursor has no source coordinate"
      let pendingSlot? ← site.localReturn.mapM fun target => do
        let (_, index) ← lookupProofBinding site.scope target.pending
        return index
      ranges := ranges.push {
        tag := request.tag, name := site.name.getId
        entryScope := request.entryScope.toArray.map fun binding => {
          name := binding.name, proofName := binding.proofName,
          type := binding.type, isMutable := binding.isMutable,
          privatePending := binding.privatePending }
        scope := site.scope.toArray.map fun binding => {
          name := binding.name, proofName := binding.proofName,
          type := binding.type, isMutable := binding.isMutable,
          privatePending := binding.privatePending }
        result := site.result, cursorSlot, stop := range.stop, stride := range.stride
        proofBody := request.proofBody
        loopProofBody := ← loopProofBody site
        bodyProofBody := range.body, bodyFallsThrough := range.fallsThrough
        localReturn := range.localReturn, pendingSlot? }
    if let some tag := site.whileRequest then
      whiles := whiles.push {
        tag, name := site.name.getId
        scope := site.scope.toArray.map fun binding => {
          name := binding.name, proofName := binding.proofName,
          type := binding.type, isMutable := binding.isMutable,
          privatePending := binding.privatePending }
        result := site.result, localReturn := site.localReturn.isSome }
    if site.guard.isSome then
      let mut rules := #["view_apply", "view_symm_apply", "captureView_apply",
        "captureView_symm_apply", "regroup_apply", "regroup_symm_apply"].map
        (loopMember site)
      let mut captures : Array LoopCaptureCoordinateRegistration := #[{
        view := loopMember site "CaptureView"
        guardFrame := loopMember site "guard_preservesCaptures"
        bodyFrame := loopMember site "body_preservesCaptures"
      }]
      if hasNativeCoordinates site then
        rules := rules ++ #[loopMember site "native_captureView_apply",
          loopMember site "native_captureView_symm_apply"]
        captures := captures.push {
          view := loopMember site "NativeCaptureView"
          guardFrame := loopMember site "native_guard_preservesCaptures"
          bodyFrame := loopMember site "native_body_preservesCaptures"
        }
      if pureMode && site.nativeResult.isSome && site.hasStandardRange then
        rules := rules ++ #[loopMember site "nativeRangeStop", loopMember site "nativeRangeStep"]
      let nativeTypes := site.scope.toArray.filterMap (fun binding => binding.native.map (·.type))
      let completion? : Option LoopCompletionCoordinateRegistration :=
        if site.localReturn.isSome then some {
          view := loopMember site "View"
          visible := loopMember site "visible"
          entry := loopMember site "entry"
          pending := loopMember site "pending"
          reconstruct := loopMember site "reconstruct"
          reconstructNone := loopMember site "reconstruct_none"
          guardFrame := loopMember site "guard_completion_frame"
          bodyFrame := loopMember site "body_ancestor_pending_frame"
          stoppedGuard := loopMember site "guard_completed"
          pendingEval := loopMember site "pending_eval"
        } else none
      coordinates := coordinates.push {
        code := loopMember site "Code"
        rules := rules
        captures := captures
        nativeTypes := nativeTypes
        completion? := completion?
      }
  return (mkNullNode declarations, (functions.map fun fn => ({
    name := fn.name.getId
    params := fn.params.map (fun param => (param.name.getId, param.type))
    result := fn.result
    pure := pureMode
    nativeHeader := fn.nativeView.map (·.header) } : FunctionInfo)), coordinates,
    { ranges, whiles })

end Core

end Complexity.Language.Syntax
