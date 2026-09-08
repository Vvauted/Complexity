/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Local.Function.Total
import Complexity.Computability.Ram.Verification.Function.Typed

/-!
# Typed observations of the actual executable function call

The source declaration's result shape decodes the fields of the existing
`Function.apply` and `Function.applyState`. These theorems transfer source
correctness without requiring clients to split lists or reconstruct an array
reference from its specification. The value and shared state come from the same
compiled run, and no extra execution relation or time budget is introduced.
-/

namespace Ram.LocalCompiler.Function

/-- A typed contract establishes normal termination of the same compiled call. -/
theorem halts_of_typedContract {α : Type*} {control heapLimit depth fn : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind} {encodeArgs : α → List (Word w)}
    {arg : α} {entry : Source.State w} {code : Code}
    {P : α → Source.State w → Prop}
    {Q : α → Source.State w → kind.Value w → Source.State w → Prop}
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (contract : Source.TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (pre : P arg entry) :
    Halts control program fn f.params heapLimit (encodeArgs arg) entry := by
  obtain ⟨value, finish, execution, _⟩ := contract arg entry pre
  exact halts_of_execution hcompile hlookup hcode hstack execution

/-- Decode the fields produced by the actual runner using a source value equation. -/
theorem applyTyped_eq_of_execution {control heapLimit depth fn : Nat} {program : Program}
    {f : Func} {kind : DSL.ValueKind} {args : List (Word w)}
    {entry finish : Source.State w} {value : kind.Value w} {code : Code}
    (shape : f.results.length = kind.width)
    (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry
      (kind.encode value) finish) :
    kind.decode («apply» control program fn f.params heapLimit args entry h)
      ((apply_length_of_lookup h hlookup).trans shape) = value :=
  kind.decode_eq_of_eq_encode _
    (apply_eq_of_execution h hcompile hlookup hcode hstack execution)

/-- Typed result and reusable shared state are projections of the same executable
call. Array fields are read from that call, not supplied by the correctness proof. -/
theorem applyStateTyped_eq_of_execution {control heapLimit depth fn : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind} {args : List (Word w)}
    {entry finish : Source.State w} {value : kind.Value w} {code : Code}
    (shape : f.results.length = kind.width)
    (h : Halts control program fn f.params heapLimit args entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (execution : Source.FunctionExec program heapLimit depth f args entry
      (kind.encode value) finish) :
    (let result := applyState control program fn f.params heapLimit args entry h;
      (kind.decode result.1 ((apply_length_of_lookup h hlookup).trans shape), result.2)) =
      (value, finish) := by
  have returned := applyState_eq_of_execution h hcompile hlookup hcode hstack execution
  have fieldsEqual :=
    congrArg (fun result : List (Word w) × Source.State w => result.1) returned
  have stateEqual :=
    congrArg (fun result : List (Word w) × Source.State w => result.2) returned
  exact Prod.ext (kind.decode_eq_of_eq_encode _ fieldsEqual) stateEqual

/-- A typed mathematical contract describes the actual executable value and
shared state without exposing its list-of-fields representation to the client. -/
theorem applyStateTyped_spec {α : Type*} {control heapLimit depth fn : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind} {encodeArgs : α → List (Word w)}
    {arg : α} {entry : Source.State w} {code : Code}
    {P : α → Source.State w → Prop}
    {Q : α → Source.State w → kind.Value w → Source.State w → Prop}
    (shape : f.results.length = kind.width)
    (h : Halts control program fn f.params heapLimit (encodeArgs arg) entry)
    (hcompile : compile control program fn f.params = some code)
    (hlookup : program[fn]? = some f) (hcode : code.length < 2 ^ w)
    (hstack : heapLimit + (depth + 1) * ABI.frameSize control < 2 ^ w)
    (contract : Source.TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (pre : P arg entry) :
    let result := applyState control program fn f.params heapLimit (encodeArgs arg) entry h
    Q arg entry (kind.decode result.1 ((apply_length_of_lookup h hlookup).trans shape)) result.2 := by
  obtain ⟨value, finish, execution, post⟩ := contract arg entry pre
  have returned := applyStateTyped_eq_of_execution shape h hcompile hlookup hcode hstack execution
  exact Eq.mpr
    (congrArg (fun result : kind.Value w × Source.State w => Q arg entry result.1 result.2) returned)
    post

end Ram.LocalCompiler.Function
