/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Basic
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Compiler.Local.Function.Total
import Complexity.Computability.Ram.Verification.Function.Typed

/-!
# Source declarations in ordinary correctness proofs

`ram_def p := ram_functions% { ... }` declares callable functions without a
main statement. `ram_def p := ram_program% { ... }` additionally supplies a
main statement. Both preserve the quoted function table and export ordinary
Lean declarations for its functions and source names:

* `p.function.f` is the actual `Ram.Func` in the table;
* `p.functionIndex.f` is the function-table index of `f`;
* `p.function_lookup.f` proves that this entry is `p.function.f`;
* `p.params_eq.f` and `p.locals_eq.f` simplify its parameter and frame-slot counts;
* `p.body_eq.f` and `p.result_eq.f` expose the lowered body and return fields;
* `p.results_length.f` proves the field count of the declared result kind;
* `p.arguments.f` takes word or `Ram.ArrayRef` parameters and constructs their word argument list;
* `p.arguments_eq.f` exposes those actual word fields to declaration-driven simplification;
* `p.arguments_length.f` proves that this list has the function's declared arity;
* `p.eval.f` observes the function's result and shared state through `Part`;
* `p.bodyTime.f` observes its compiler-derived body count through `Part`;
* `p.run.f` executes its compiled call without a supplied instruction limit;
* `p.runTotal.f` executes a call proved to halt and retains its complete machine result;
* `p.apply.f` projects that call's declared `Word`, `ArrayRef` or `Unit` value;
* `p.applyState.f` returns its typed value together with the resulting source shared state;
* `p.localReg.f.x` is the binding of `x` visible at the return of function `f`;
* `p.mainReg.x` is a binding visible at the end of `main`, when present.

An array parameter or local binding `xs` exports `p.localReg.f.xs.base` and
`p.localReg.f.xs.length`. The typed argument builder passes those same two
words; it does not allocate or load an in-memory descriptor.

The generated `eval`, `bodyTime` and `run` take the declared word or array
parameters first, then a heap capacity and an existing source state. The first
two are noncomputable observations of the same function, not executable
specifications. `run` retains the complete machine result, including its shared
memory, input/output, stopping status and count. Its code and stack
representability premises are those of the existing function runner; generating
an entry point does not discharge them. A diverging unbounded call does not return.

`runTotal`, `apply` and `applyState` take the same typed parameters, heap capacity and entry
state, followed by a `Ram.LocalCompiler.Function.Halts` proof. This establishes
normal halt, not merely the presence of an optional result: faults are not
successful function returns. The proof is erased at runtime; these entry points
execute the existing runner, rather than extracting a value from a specification.
Use `runTotal` to retain the actual machine state and transition count;
`apply` projects only the declared value. Its word/array fields come from the
actual runner, with their length justified by the function declaration; missing
fields are never replaced by default words. None requires a time budget.

The projection of a Unit result is `()`. Observing only that empty value cannot
force a pure host computation to execute: use `applyState` for shared effects or
`runTotal` for the state and count. This does not elide source Unit calls, whose
bodies, effects and frame handling execute through the same compiled ABI.

`applyState` pairs the declared result type with `Ram.Source.State w`. Its state restores the caller's
registers, takes the executed heap contents below the heap boundary, and retains
the entry memory outside it, so private target stack cells do not become source
heap contents. Actual input/output effects are retained. This is a projection of
the same execution, not a new executor or an array loader; its cost remains the
transition count exposed by `runTotal`.

Thus contracts can use `s.regs p.localReg.f.x` and `s.setReg p.mainReg.x value`
without reproducing register numbers. The register abbreviations use the
surface language's own lowering, including parameter-before-local allocation
and lexical shadowing. Nested block locals do not escape their blocks and are
not exported as function-level names. Function indices use declaration order,
exactly as named calls do. Function names, function locals and main locals remain in
separate namespaces; the usual Lean declaration-name collision errors apply.

Function abbreviations select the quoted table entry. Body and result equations
reuse terms from that same lowering, so proofs can unfold source definitions
without maintaining a second syntax tree. The command and term quotations invoke
the same lowering once, sharing name resolution, slot allocation and generated AST.
No runtime lookup is introduced, and the compiler and verification rules are unchanged.
Existing term-form declarations need not be migrated.

The dedicated `ram_bindings` simp set contains the generated argument-field
equations, lookup and static arity/frame/result counts. RAM verification tactics
use these facts for both local and imported functions, so callers need not repeat
argument-builder definitions or declaration lookup proofs. Bodies and returned
expressions are not registered: opening an implementation still requires its
explicit body/result equations. Mathematical specifications and representation
lemmas are not added to this set.

Within `ram_def`, `include other as Alias;` imports a previously declared collection
before the local functions. Calls such as `Alias.f(xs)` retain the imported word/array
parameter and result signature. Linking relocates every imported internal call; local functions are lowered
once with their final indices. `p.importMap.Alias` and `p.embeds.Alias` expose the index
map and semantic embedding. Imported members receive the same function, argument and
runtime entries under `p.function.Alias.f`, `p.arguments.Alias.f`, `p.run.Alias.f`, and so
on. Their source bodies are not lowered again. Retained signature metadata also includes
imported members, so an already linked collection can itself be included later. Includes
require `ram_def`; ordinary term quotations without includes remain unchanged.
-/

namespace Ram.DSL

open Lean.Parser.Term

private def valueKindTerm : ValueKind → Lean.MacroM (Lean.TSyntax `term)
  | .word => `(Ram.DSL.ValueKind.word)
  | .array => `(Ram.DSL.ValueKind.array)
  | .unit => `(Ram.DSL.ValueKind.unit)

/-- Source signatures persist across imports; the executable definitions remain the
ordinary named function tables. No function bodies are stored in this extension. -/
initialize functionSignatures :
    Lean.SimplePersistentEnvExtension (Lean.Name × Array FunctionSignature)
      (Lean.NameMap (Array FunctionSignature)) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun modules => modules.foldl
      (fun state entries => entries.foldl
        (fun state entry => state.insert entry.1 entry.2) state) {}
    addEntryFn := fun state entry => state.insert entry.1 entry.2 }

/-- Lexical proof locations for locally declared function bodies. These are
metadata from the original lowering, not a second executable representation.
Keys are the generated function declaration names. Imported bodies keep their
original declaration's sites; their linked copies are not lowered again. -/
initialize functionProofSites :
    Lean.SimplePersistentEnvExtension (Lean.Name × Array ProofSite)
      (Lean.NameMap (Array ProofSite)) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun modules => modules.foldl
      (fun state entries => entries.foldl
        (fun state entry => state.insert entry.1 entry.2) state) {}
    addEntryFn := fun state entry => state.insert entry.1 entry.2 }

private def localRegisterDeclarations (scopeName : Lean.Name)
    (scope : LocalScope) : Lean.MacroM (Array Lean.Syntax) := do
  let declare (name : Lean.Name) (index : Nat) := do
    let register := Lean.Syntax.mkNumLit (toString index)
    let registerName := Lean.mkIdent (scopeName ++ name)
    let declaration ← `(command| abbrev $registerName:ident : Ram.Reg := $register:num)
    pure declaration.raw
  let mut declarations := #[]
  for binding in scope do
    match binding.kind with
    | .word => declarations := declarations.push (← declare binding.name binding.register)
    | .array =>
        declarations := declarations.push (← declare (binding.name ++ `base) binding.register)
        declarations := declarations.push
          (← declare (binding.name ++ `length) (binding.register + 1))
    | .unit => pure ()
  return declarations

private def argumentDeclarations (name fn : Lean.TSyntax `ident)
    (params : Array Parameter) (functionName : Lean.TSyntax `ident) :
    Lean.MacroM (Array Lean.Syntax) := do
  let argumentsName := Lean.mkIdentFrom fn (name.getId ++ `arguments ++ fn.getId)
  let equationName := Lean.mkIdentFrom fn (name.getId ++ `arguments_eq ++ fn.getId)
  let lengthName := Lean.mkIdentFrom fn (name.getId ++ `arguments_length ++ fn.getId)
  let width := Lean.mkIdent (← Lean.Macro.addMacroScope `w)
  let parameterType (kind : ValueKind) := match kind with
    | .word => `(Ram.Word $width:ident)
    | .array => `(Ram.ArrayRef $width:ident)
    | .unit => `(Unit)
  let mut words : Array (Lean.TSyntax `term) := #[]
  for param in params do
    let name := param.name
    match param.kind with
    | .word => words := words.push (← `($name:ident))
    | .array =>
        words := words.push (← `(($name:ident).base))
        words := words.push (← `(($name:ident).length))
    | .unit => pure ()
  let mut value ← `(([$words,*] : List (Ram.Word $width:ident)))
  for param in params.reverse do
    let name := param.name
    value ← `(fun ($name:ident : $(← parameterType param.kind)) => $value)
  let arguments ← `(command| abbrev $argumentsName:ident {$width:ident : Nat} := $value)
  let mut application ← `(@$argumentsName:ident $width:ident)
  for param in params do
    let name := param.name
    application ← `($application $name:ident)
  let mut arity ← `(($application).length = ($functionName:ident).params)
  let mut proof ← `(Eq.refl ($application).length)
  let mut fieldsEquation ← `($application = ([$words,*] : List (Ram.Word $width:ident)))
  let mut fieldsProof ← `(Eq.refl $application)
  for param in params.reverse do
    let name := param.name
    let type ← parameterType param.kind
    arity ← `(∀ ($name:ident : $type), $arity)
    proof ← `(fun ($name:ident : $type) => $proof)
    fieldsEquation ← `(∀ ($name:ident : $type), $fieldsEquation)
    fieldsProof ← `(fun ($name:ident : $type) => $fieldsProof)
  let equation ← `(command|
    /-- The declared parameters' actual by-value word fields. -/
    @[ram_bindings] theorem $equationName:ident {$width:ident : Nat} :
      $fieldsEquation := $fieldsProof)
  let length ← `(command| @[ram_bindings] theorem $lengthName:ident
    {$width:ident : Nat} : $arity := $proof)
  return #[arguments.raw, equation.raw, length.raw]

private def functionEntryPoints (name fn functionName : Lean.TSyntax `ident)
    (params : Array Parameter) (resultKind : ValueKind) :
    Lean.MacroM (Array Lean.Syntax) := do
  let argumentsName := Lean.mkIdentFrom fn (name.getId ++ `arguments ++ fn.getId)
  let indexName := Lean.mkIdentFrom fn (name.getId ++ `functionIndex ++ fn.getId)
  let lookupName := Lean.mkIdentFrom fn (name.getId ++ `function_lookup ++ fn.getId)
  let resultLengthName := Lean.mkIdentFrom fn (name.getId ++ `results_length ++ fn.getId)
  let evalName := Lean.mkIdentFrom fn (name.getId ++ `eval ++ fn.getId)
  let timeName := Lean.mkIdentFrom fn (name.getId ++ `bodyTime ++ fn.getId)
  let runName := Lean.mkIdentFrom fn (name.getId ++ `run ++ fn.getId)
  let runTotalName := Lean.mkIdentFrom fn (name.getId ++ `runTotal ++ fn.getId)
  let applyName := Lean.mkIdentFrom fn (name.getId ++ `apply ++ fn.getId)
  let applyStateName := Lean.mkIdentFrom fn (name.getId ++ `applyState ++ fn.getId)
  let width := Lean.mkIdent (← Lean.Macro.addMacroScope `w)
  let heapLimit := Lean.mkIdent (← Lean.Macro.addMacroScope `heapLimit)
  let entry := Lean.mkIdent (← Lean.Macro.addMacroScope `entry)
  let halts := Lean.mkIdent (← Lean.Macro.addMacroScope `halts)
  let kind ← valueKindTerm resultKind
  let mut arguments ← `(@$argumentsName:ident $width:ident)
  for param in params do
    let parameter := param.name
    arguments ← `($arguments $parameter:ident)
  let mut eval ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.Func.evalTyped $functionName:ident $kind $resultLengthName:ident
      ($name:ident).program $heapLimit:ident $arguments $entry:ident)
  let mut time ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.Func.bodyTime $functionName:ident ($name:ident).program $heapLimit:ident
      $arguments $entry:ident)
  let mut run ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.LocalCompiler.Function.runUntil (max 1 ($name:ident).registers)
      ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
      $arguments $entry:ident)
  let mut runTotal ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.LocalCompiler.Function.runTotal (max 1 ($name:ident).registers)
      ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
      $arguments $entry:ident)
  let mut application ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    fun ($halts:ident : Ram.LocalCompiler.Function.Halts (max 1 ($name:ident).registers)
        ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
        $arguments $entry:ident) =>
      Ram.DSL.ValueKind.decode $kind
        (Ram.LocalCompiler.Function.apply (max 1 ($name:ident).registers)
          ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
          $arguments $entry:ident $halts:ident)
        ((Ram.LocalCompiler.Function.apply_length_of_lookup $halts:ident
          $lookupName:ident).trans $resultLengthName:ident))
  let mut applicationState ← `(fun ($heapLimit:ident : Nat)
      ($entry:ident : Ram.Source.State $width:ident) =>
    fun ($halts:ident : Ram.LocalCompiler.Function.Halts (max 1 ($name:ident).registers)
        ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
        $arguments $entry:ident) =>
      let result := Ram.LocalCompiler.Function.applyState (max 1 ($name:ident).registers)
        ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
        $arguments $entry:ident $halts:ident
      (Ram.DSL.ValueKind.decode $kind result.1
        (show result.1.length = ($kind).width from
          (Ram.LocalCompiler.Function.apply_length_of_lookup $halts:ident
            $lookupName:ident).trans $resultLengthName:ident), result.2))
  for param in params.reverse do
    let parameter := param.name
    let type ← match param.kind with
      | .word => `(Ram.Word $width:ident)
      | .array => `(Ram.ArrayRef $width:ident)
      | .unit => `(Unit)
    eval ← `(fun ($parameter:ident : $type) => $eval)
    time ← `(fun ($parameter:ident : $type) => $time)
    run ← `(fun ($parameter:ident : $type) => $run)
    runTotal ← `(fun ($parameter:ident : $type) => $runTotal)
    application ← `(fun ($parameter:ident : $type) => $application)
    applicationState ← `(fun ($parameter:ident : $type) => $applicationState)
  let evalDeclaration ← `(command|
    /-- The declared function's result and shared state, observed through its actual execution. -/
    noncomputable abbrev $evalName:ident {$width:ident : Nat} := $eval)
  let timeDeclaration ← `(command|
    /-- The declared function's compiled body count, excluding its enclosing call overhead. -/
    noncomputable abbrev $timeName:ident {$width:ident : Nat} := $time)
  let runDeclaration ← `(command|
    /-- Execute the declared function's compiled call, retaining the complete machine result. -/
    abbrev $runName:ident {$width:ident : Nat} := $run)
  let runTotalDeclaration ← `(command|
    /-- Execute the declared function with a normal-halt proof, retaining its state and count. -/
    abbrev $runTotalName:ident {$width:ident : Nat} := $runTotal)
  let applyDeclaration ← `(command|
    /-- Project the declared word, array, or Unit result of the normally terminating call.
    Use `runTotal` or `applyState` to observe execution when the result is Unit. -/
    abbrev $applyName:ident {$width:ident : Nat} := $application)
  let applyStateDeclaration ← `(command|
    /-- Execute the declared function and return its typed value and source shared state, excluding
    private stack cells and restoring caller registers while retaining actual stream effects. -/
    abbrev $applyStateName:ident {$width:ident : Nat} := $applicationState)
  return #[evalDeclaration.raw, timeDeclaration.raw, runDeclaration.raw,
    runTotalDeclaration.raw, applyDeclaration.raw, applyStateDeclaration.raw]

private def layoutEquations (name fn functionName : Lean.TSyntax `ident)
    (params locals : Lean.TSyntax `term) : Lean.MacroM (Array Lean.Syntax) := do
  let paramsName := Lean.mkIdentFrom fn (name.getId ++ `params_eq ++ fn.getId)
  let paramsEquation ← `(command| @[simp, ram_bindings] theorem $paramsName:ident :
    ($functionName:ident).params = $params := rfl)
  let localsName := Lean.mkIdentFrom fn (name.getId ++ `locals_eq ++ fn.getId)
  let localsEquation ← `(command| @[simp, ram_bindings] theorem $localsName:ident :
    ($functionName:ident).locals = $locals := rfl)
  return #[paramsEquation.raw, localsEquation.raw]

private def resultLengthEquation (name fn functionName : Lean.TSyntax `ident)
    (kind : ValueKind) : Lean.MacroM Lean.Syntax := do
  let lengthName := Lean.mkIdentFrom fn (name.getId ++ `results_length ++ fn.getId)
  let width := Lean.Syntax.mkNumLit (toString kind.width)
  let declaration ← `(command| @[simp, ram_bindings] theorem $lengthName:ident :
    ($functionName:ident).results.length = $width:num := rfl)
  return declaration.raw

private def functionEquations (name fn functionName : Lean.TSyntax `ident)
    (lowered : Lean.TSyntax `term) (kind : ValueKind) :
    Lean.MacroM (Array Lean.Syntax) := do
  match lowered with
  | `(($_label:str, Ram.Func.mk $params:term $locals:term $body:term $result:term)) =>
      let bodyName := Lean.mkIdentFrom fn (name.getId ++ `body_eq ++ fn.getId)
      let bodyEquation ← `(command| theorem $bodyName:ident :
        ($functionName:ident).body = $body := rfl)
      let resultName := Lean.mkIdentFrom fn (name.getId ++ `result_eq ++ fn.getId)
      let resultEquation ← `(command| theorem $resultName:ident :
        ($functionName:ident).results = $result := rfl)
      return (← layoutEquations name fn functionName params locals) ++
        #[bodyEquation.raw, resultEquation.raw,
          ← resultLengthEquation name fn functionName kind]
  | _ => Lean.Macro.throwErrorAt lowered "expected a lowered RAM function"

private def functionDeclarations (name : Lean.TSyntax `ident)
    (decls : Array FunctionDeclaration) (functions : Array (Lean.TSyntax `term))
    (scopes : Array LocalScope) (offset : Nat) :
    Lean.MacroM (Array Lean.Syntax) := do
  let mut declarations := #[]
  let mut index := offset
  for ((decl, lowered), scope) in (decls.zip functions).zip scopes do
    let fn := decl.name
    let indexName := Lean.mkIdentFrom fn (name.getId ++ `functionIndex ++ fn.getId)
    let literal := Lean.Syntax.mkNumLit (toString index)
    let functionIndex ← `(command| abbrev $indexName:ident : Nat := $literal:num)
    declarations := declarations.push functionIndex.raw
    let functionName := Lean.mkIdentFrom fn (name.getId ++ `function ++ fn.getId)
    let function ← `(command| abbrev $functionName:ident : Ram.Func :=
      ($name:ident).program[$indexName:ident]'(by decide))
    declarations := declarations.push function.raw
    let lookupName := Lean.mkIdentFrom fn (name.getId ++ `function_lookup ++ fn.getId)
    let lookup ← `(command| @[ram_bindings] theorem $lookupName:ident :
      ($name:ident).program[$indexName:ident]? = some $functionName:ident := by rfl)
    declarations := declarations.push lookup.raw
    declarations := declarations ++ (← functionEquations name fn functionName lowered decl.resultKind)
    declarations := declarations ++ (← argumentDeclarations name fn decl.params functionName)
    declarations := declarations ++
      (← functionEntryPoints name fn functionName decl.params decl.resultKind)
    declarations := declarations ++ (← localRegisterDeclarations
      (name.getId ++ `localReg ++ fn.getId) scope)
    index := index + 1
  return declarations

private def importDeclarations (name : Lean.TSyntax `ident) (lowered : LoweredNamed)
    (sourceNames : Array Lean.Name) :
    Lean.MacroM (Array Lean.Syntax) := do
  let mut declarations := #[]
  for position in [:lowered.imports.size] do
    let dependency := lowered.imports[position]!
    let src := dependency.source
    let importAlias := dependency.alias
    let before := lowered.prefixes[position]!
    let label := Lean.Syntax.mkStrLit importAlias.getId.toString
    let mapName := Lean.mkIdentFrom importAlias (name.getId ++ `importMap ++ importAlias.getId)
    let embeddingName := Lean.mkIdentFrom importAlias (name.getId ++ `embeds ++ importAlias.getId)
    let indexMap ← `(command| abbrev $mapName:ident : Nat → Nat :=
      fun i => ($before).program.length + i)
    declarations := declarations.push indexMap.raw
    let mut embedding ← `(Ram.Named.Functions.embeds_link_right $before
      (Ram.Named.Functions.mk ($src:ident).registers ($src:ident).declarations) $label:str)
    for laterPosition in [position + 1:lowered.imports.size] do
      let later := lowered.imports[laterPosition]!
      let laterSource := later.source
      let laterLabel := Lean.Syntax.mkStrLit later.alias.getId.toString
      let laterPrefix := lowered.prefixes[laterPosition]!
      embedding ← `(Ram.Program.Embeds.trans (ρ := $mapName:ident) (σ := id) $embedding
        (Ram.Named.Functions.embeds_link_left $laterPrefix
          (Ram.Named.Functions.mk ($laterSource:ident).registers
            ($laterSource:ident).declarations) $laterLabel:str))
    let linked := lowered.prefixes[lowered.imports.size]!
    let registers := Lean.Syntax.mkNumLit (toString lowered.localRegisters)
    let locals := lowered.functions
    embedding ← `(Ram.Program.Embeds.trans (ρ := $mapName:ident) (σ := id) $embedding
      (Ram.Named.Functions.embeds_extend $linked $registers:num [$locals,*]))
    let embeddingDeclaration ← `(command| theorem $embeddingName:ident :
      Ram.Program.Embeds $mapName:ident ($src:ident).program ($name:ident).program := $embedding)
    declarations := declarations.push embeddingDeclaration.raw
    for index in [:dependency.signatures.size] do
      let signature := dependency.signatures[index]!
      let fn := Lean.mkIdentFrom importAlias (importAlias.getId ++ signature.name)
      let indexName := Lean.mkIdentFrom fn (name.getId ++ `functionIndex ++ fn.getId)
      let functionName := Lean.mkIdentFrom fn (name.getId ++ `function ++ fn.getId)
      let lookupName := Lean.mkIdentFrom fn (name.getId ++ `function_lookup ++ fn.getId)
      let literal := Lean.Syntax.mkNumLit (toString index)
      let original ← `(($src:ident).program[$literal:num]'(by decide))
      let indexDeclaration ← `(command| abbrev $indexName:ident : Nat := $mapName:ident $literal:num)
      let functionDeclaration ← `(command| abbrev $functionName:ident : Ram.Func :=
        ($original).renameCalls $mapName:ident)
      let lookupDeclaration ← `(command| @[ram_bindings] theorem $lookupName:ident :
        ($name:ident).program[$indexName:ident]? = some $functionName:ident :=
        $embeddingName:ident (show ($src:ident).program[$literal:num]? = some $original from rfl))
      declarations := declarations ++
        #[indexDeclaration.raw, functionDeclaration.raw, lookupDeclaration.raw]
      let originalName := Lean.mkCIdentFrom src
        (sourceNames[position]! ++ `function ++ signature.name)
      declarations := declarations ++ (← layoutEquations name fn functionName
        (← `(($originalName:ident).params)) (← `(($originalName:ident).locals)))
      declarations := declarations.push
        (← resultLengthEquation name fn functionName signature.result)
      let params : Array Parameter := signature.params.map fun (parameter, kind) =>
        { name := Lean.mkIdent parameter, kind := kind }
      declarations := declarations ++ (← argumentDeclarations name fn params functionName)
      declarations := declarations ++
        (← functionEntryPoints name fn functionName params signature.result)
  return declarations

/-- Declare named RAM functions or a named bundle, exporting their functions,
lookup theorems and source-level variable names for ordinary correctness proofs. -/
syntax (name := ramDef) (docComment)? "ram_def " ident " := " term : command

elab_rules : command
  | `(command| $[$doc:docComment]? ram_def $name:ident := $source:term) => do
      let parsed ← Lean.Elab.liftMacroM (parseNamed source)
      let mut imports : Array FunctionImport := #[]
      let mut sourceNames : Array Lean.Name := #[]
      for dependency in parsed.includes do
        match dependency with
        | `(ramInclude| include $src:ident as $importAlias:ident;) =>
            let resolved ← Lean.resolveGlobalConstNoOverload src
            let some signatures := (functionSignatures.getState (← Lean.getEnv)).find? resolved
              | Lean.throwErrorAt src "included collection must be declared with 'ram_def'"
            imports := imports.push ⟨src, importAlias, signatures⟩
            sourceNames := sourceNames.push resolved
        | _ => Lean.throwErrorAt dependency "expected 'include collection as Alias;'"
      let lowered ← Lean.Elab.liftMacroM (lowerNamed source imports)
      let declarations ← Lean.Elab.liftMacroM do
        let declaration ← `(command| $[$doc:docComment]? def $name:ident :
          $(lowered.type) := $(lowered.term))
        let mut declarations := #[declaration.raw] ++
          (← importDeclarations name lowered sourceNames)
        declarations := declarations ++ (← functionDeclarations name
          lowered.parsed lowered.functions lowered.functionScopes lowered.localOffset)
        declarations := declarations ++ (← localRegisterDeclarations
          (name.getId ++ `mainReg) lowered.mainScope)
        pure (Lean.mkNullNode declarations)
      Lean.Elab.Command.elabCommand declarations
      let resolved ← Lean.resolveGlobalConstNoOverload name
      Lean.modifyEnv (functionSignatures.addEntry · (resolved, lowered.signatures))
      for (decl, sites) in lowered.parsed.zip lowered.functionProofSites do
        let functionName := resolved ++ `function ++ decl.name.getId
        Lean.modifyEnv (functionProofSites.addEntry · (functionName, sites))

end Ram.DSL
