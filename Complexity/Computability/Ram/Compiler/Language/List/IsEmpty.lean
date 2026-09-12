/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.List.Basic
import Complexity.Computability.Ram.Compiler.Language.FunctionExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound

/-!
# Compiling emptiness of represented linked lists

The source operation branches on the optional root already passed to the
function. It neither allocates nor reads a node. A present root is copied as
one actual placed address; its mathematical object identifier is not required
to fit the machine word width.

The body budget is inferred from the existing match and return cost rules.
The public execution theorem applies the independent ordinary `List.isEmpty`
contract to the same halted RAM invocation and includes its actual outer-call
and halt overhead. Input loading remains outside this preloaded-call boundary.
-/

namespace Ram.LanguageCompiler.List.IsEmpty

open Complexity.Language
open Complexity.Language.List.IsEmpty

/-- Reading the optional-root tag needs a positive word width, but no heap
access, node-identifier range or nested source call. -/
theorem realizable (kind : CellTy) {w : Nat} (hw : 0 < w) :
    FunctionRealizable (program kind) w 0 (entry kind) (fun _ _ => True) := by
  intro args heap _
  change ∃ finish value,
    RealizedExec (program kind) w 0 (body kind) ⟨args, heap⟩ finish (.returned value)
  cases selected : args.head with
  | none =>
      refine ⟨⟨args, heap⟩, true, .matchNone selected ?_⟩
      exact .ret (.bool true) ⟨args, heap⟩
        (Nat.one_lt_two_pow (Nat.ne_of_gt hw))
  | some ref =>
      refine ⟨⟨args, heap⟩, false, ?_⟩
      exact .matchSome (entry := ⟨args, heap⟩) (payload := ref)
        (value := .var .here) selected (by trivial)
        (.ret (.bool false) (Complexity.Language.State.cons ref ⟨args, heap⟩)
          (Nat.two_pow_pos w))

/-- Infer an input-independent certificate from the actual branch and return
rules. The present branch includes copying its one real payload word. -/
def bodyCost (kind : CellTy) : { bound : Nat //
    ∀ initial : Complexity.Language.State [.option (.node kind)],
      StmtCostBound (program kind) (body kind) initial bound } := ⟨_, by
  intro initial
  exact StmtCostBound.match_max
    (fun _ => StmtCostBound.ret (.bool true) initial)
    (fun payload _ => StmtCostBound.ret (.bool false)
      (Complexity.Language.State.cons payload initial))⟩

/-- The function rule adds the compiler's return-flag initialization once. -/
theorem costBound (kind : CellTy) :
    FunctionCostBound (program kind) (entry kind) (fun _ _ => True)
      (fun _ _ => (bodyCost kind).val + 2) :=
  FunctionCostBound.of_stmt (fun args heap _ => (bodyCost kind).property ⟨args, heap⟩)

/-- Neither branch writes or allocates shared heap objects. -/
theorem program_noHeapWrites (kind : CellTy) :
    ∀ fn, NoHeapWrites ((program kind).body fn) := by
  intro fn
  refine Fin.cases ?_ (fun index => Fin.elim0 index) fn
  change NoHeapWrites (body kind)
  simp [body, NoHeapWrites]

/-- The inferred body budget plus the existing outer-call and final-halt
charges, with no separately chosen instruction prices. -/
def steps (kind : CellTy) : Nat :=
  LocalCompiler.Function.callSteps (programControl (program kind))
    (lowerFunc (program kind) (entry kind)) ((bodyCost kind).val + 2) + 1

/-- The same actual halted invocation returns ordinary list emptiness. Code,
one stack frame and the complete represented heap must fit; argument loading
is outside this boundary. No node traversal or allocation is hidden in it. -/
theorem execute_le (kind : CellTy) {w heapLimit : Nat}
    (values : _root_.List (CellValue kind)) (root : Option (NodeRef kind))
    (initialHeap : Heap) (initial : Source.State w) (placement : Nat → Word w)
    (capacity : FunctionCapacity (program kind) (entry kind) w 0 heapLimit)
    (memory : HeapRep placement heapLimit initialHeap initial)
    (observed : (Representation.list kind).Rel values root initialHeap) :
    ∃ outcome : FunctionExecution (program kind) (entry kind) heapLimit placement
        (Env.cons (τ := .option (.node kind)) root Env.empty) initialHeap initial,
      outcome.value = values.isEmpty ∧
      outcome.heap = initialHeap ∧
      Source.State.Observes heapLimit 0 initial outcome.result.state ∧
      outcome.result.steps ≤ steps kind := by
  let args : Env [.option (.node kind)] := Env.cons root Env.empty
  have arguments : EnvFits w args := by
    refine EnvFits.cons (τ := .option (.node kind)) (EnvFits.empty w) root ?_
    cases root with
    | none => trivial
    | some ref => exact ⟨Nat.one_lt_two_pow (Nat.ne_of_gt capacity.positive), trivial⟩
  let launch : FunctionLaunch (program kind) (entry kind) 0 heapLimit placement
      args initialHeap initial := ⟨capacity, arguments, memory⟩
  obtain ⟨outcome, property, bounded⟩ :=
    (realizable kind capacity.positive).execute_le
      (total kind values) (costBound kind) launch trivial observed trivial
  exact ⟨outcome, property.1, property.2,
    outcome.observes_of_noHeapWrites (program_noHeapWrites kind), bounded⟩

end Ram.LanguageCompiler.List.IsEmpty
