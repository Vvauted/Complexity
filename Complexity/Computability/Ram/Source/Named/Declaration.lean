/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Named.Basic
import Complexity.Computability.Ram.Array.Ref
import Complexity.Computability.Ram.Compiler.Local.Function.Total

/-!
# Source declarations in ordinary correctness proofs

`ram_def p := ram_functions% { ... }` declares callable functions without a
main statement. `ram_def p := ram_program% { ... }` additionally supplies a
main statement. Both preserve the quoted function table and export ordinary
Lean declarations for its functions and source names:

* `p.function.f` is the actual `Ram.Func` in the table;
* `p.functionIndex.f` is the function-table index of `f`;
* `p.function_lookup.f` proves that this entry is `p.function.f`;
* `p.body_eq.f` and `p.result_eq.f` expose the lowered body and return expression;
* `p.arguments.f` takes word or `Ram.ArrayRef` parameters and constructs their word argument list;
* `p.arguments_length.f` proves that this list has the function's declared arity;
* `p.eval.f` observes the function's result and shared state through `Part`;
* `p.bodyTime.f` observes its compiler-derived body count through `Part`;
* `p.run.f` executes its compiled call without a supplied instruction limit;
* `p.runTotal.f` executes a call proved to halt and retains its complete machine result;
* `p.apply.f` returns that call's word value as an ordinary executable function;
* `p.applyState.f` returns its word value together with the resulting source shared state;
* `p.localReg.f.x` is the binding of `x` visible at the return of function `f`;
* `p.mainReg.x` is a binding visible at the end of `main`, when present.

An array parameter `xs` exports `p.localReg.f.xs.base` and
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
`apply` projects only the returned word. None requires a time budget.

`applyState` returns `Word w × Ram.Source.State w`. Its state restores the caller's
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
-/

namespace Ram.DSL

open Lean.Parser.Term

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
  return declarations

private def argumentDeclarations (name fn : Lean.TSyntax `ident)
    (params : Array Parameter) (functionName : Lean.TSyntax `ident) :
    Lean.MacroM (Array Lean.Syntax) := do
  let argumentsName := Lean.mkIdentFrom fn (name.getId ++ `arguments ++ fn.getId)
  let lengthName := Lean.mkIdentFrom fn (name.getId ++ `arguments_length ++ fn.getId)
  let width := Lean.mkIdent (← Lean.Macro.addMacroScope `w)
  let parameterType (kind : ParameterKind) := match kind with
    | .word => `(Ram.Word $width:ident)
    | .array => `(Ram.ArrayRef $width:ident)
  let mut words : Array (Lean.TSyntax `term) := #[]
  for param in params do
    let name := param.name
    match param.kind with
    | .word => words := words.push (← `($name:ident))
    | .array =>
        words := words.push (← `(($name:ident).base))
        words := words.push (← `(($name:ident).length))
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
  for param in params.reverse do
    let name := param.name
    let type ← parameterType param.kind
    arity ← `(∀ ($name:ident : $type), $arity)
    proof ← `(fun ($name:ident : $type) => $proof)
  let length ← `(command| theorem $lengthName:ident {$width:ident : Nat} : $arity := $proof)
  return #[arguments.raw, length.raw]

private def functionEntryPoints (name fn functionName : Lean.TSyntax `ident)
    (params : Array Parameter) : Lean.MacroM (Array Lean.Syntax) := do
  let argumentsName := Lean.mkIdentFrom fn (name.getId ++ `arguments ++ fn.getId)
  let indexName := Lean.mkIdentFrom fn (name.getId ++ `functionIndex ++ fn.getId)
  let evalName := Lean.mkIdentFrom fn (name.getId ++ `eval ++ fn.getId)
  let timeName := Lean.mkIdentFrom fn (name.getId ++ `bodyTime ++ fn.getId)
  let runName := Lean.mkIdentFrom fn (name.getId ++ `run ++ fn.getId)
  let runTotalName := Lean.mkIdentFrom fn (name.getId ++ `runTotal ++ fn.getId)
  let applyName := Lean.mkIdentFrom fn (name.getId ++ `apply ++ fn.getId)
  let applyStateName := Lean.mkIdentFrom fn (name.getId ++ `applyState ++ fn.getId)
  let width := Lean.mkIdent (← Lean.Macro.addMacroScope `w)
  let heapLimit := Lean.mkIdent (← Lean.Macro.addMacroScope `heapLimit)
  let entry := Lean.mkIdent (← Lean.Macro.addMacroScope `entry)
  let mut arguments ← `(@$argumentsName:ident $width:ident)
  for param in params do
    let parameter := param.name
    arguments ← `($arguments $parameter:ident)
  let mut eval ← `(fun ($heapLimit:ident : Nat) ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.Func.eval $functionName:ident ($name:ident).program $heapLimit:ident
      $arguments $entry:ident)
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
    Ram.LocalCompiler.Function.apply (max 1 ($name:ident).registers)
      ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
      $arguments $entry:ident)
  let mut applicationState ← `(fun ($heapLimit:ident : Nat)
      ($entry:ident : Ram.Source.State $width:ident) =>
    Ram.LocalCompiler.Function.applyState (max 1 ($name:ident).registers)
      ($name:ident).program $indexName:ident ($functionName:ident).params $heapLimit:ident
      $arguments $entry:ident)
  for param in params.reverse do
    let parameter := param.name
    let type ← match param.kind with
      | .word => `(Ram.Word $width:ident)
      | .array => `(Ram.ArrayRef $width:ident)
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
    /-- Execute the declared function with a normal-halt proof and return its word value. -/
    abbrev $applyName:ident {$width:ident : Nat} := $application)
  let applyStateDeclaration ← `(command|
    /-- Execute the declared function and return its word and source shared state, excluding
    private stack cells and restoring caller registers while retaining actual stream effects. -/
    abbrev $applyStateName:ident {$width:ident : Nat} := $applicationState)
  return #[evalDeclaration.raw, timeDeclaration.raw, runDeclaration.raw,
    runTotalDeclaration.raw, applyDeclaration.raw, applyStateDeclaration.raw]

private def functionEquations (name fn functionName : Lean.TSyntax `ident)
    (lowered : Lean.TSyntax `term) : Lean.MacroM (Array Lean.Syntax) := do
  match lowered with
  | `(($_label:str, Ram.Func.mk $_params:term $_locals:term $body:term $result:term)) =>
      let bodyName := Lean.mkIdentFrom fn (name.getId ++ `body_eq ++ fn.getId)
      let bodyEquation ← `(command| theorem $bodyName:ident :
        ($functionName:ident).body = $body := rfl)
      let resultName := Lean.mkIdentFrom fn (name.getId ++ `result_eq ++ fn.getId)
      let resultEquation ← `(command| theorem $resultName:ident :
        ($functionName:ident).result = $result := rfl)
      return #[bodyEquation.raw, resultEquation.raw]
  | _ => Lean.Macro.throwErrorAt lowered "expected a lowered RAM function"

private def functionDeclarations (name : Lean.TSyntax `ident)
    (decls : Array FunctionDeclaration) (functions : Array (Lean.TSyntax `term))
    (scopes : Array LocalScope) :
    Lean.MacroM (Array Lean.Syntax) := do
  let mut declarations := #[]
  let mut index := 0
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
    let lookup ← `(command| theorem $lookupName:ident :
      ($name:ident).program[$indexName:ident]? = some $functionName:ident := by rfl)
    declarations := declarations.push lookup.raw
    declarations := declarations ++ (← functionEquations name fn functionName lowered)
    declarations := declarations ++ (← argumentDeclarations name fn decl.params functionName)
    declarations := declarations ++ (← functionEntryPoints name fn functionName decl.params)
    declarations := declarations ++ (← localRegisterDeclarations
      (name.getId ++ `localReg ++ fn.getId) scope)
    index := index + 1
  return declarations

/-- Declare named RAM functions or a named bundle, exporting their functions,
lookup theorems and source-level variable names for ordinary correctness proofs. -/
syntax (name := ramDef) (docComment)? "ram_def " ident " := " term : command

macro_rules
  | `(command| $[$doc:docComment]? ram_def $name:ident := $source:term) => do
      let lowered ← lowerNamed source
      let declaration ← `(command| $[$doc:docComment]? def $name:ident :
        $(lowered.type) := $(lowered.term))
      let mut declarations := #[declaration.raw] ++ (← functionDeclarations name
        lowered.parsed lowered.functions lowered.functionScopes)
      declarations := declarations ++ (← localRegisterDeclarations
        (name.getId ++ `mainReg) lowered.mainScope)
      return Lean.mkNullNode declarations

end Ram.DSL
