/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.List.Cons
import Complexity.Computability.Ram.Compiler.Language.Arena.Linking

/-!
# Calling the linked-list constructor

A caller that returns the result of an imported constructor retains the same
actual allocation and cursor. This connects the existing constructor proof to
the existing call and return rules; it does not introduce another implementation
or assign a new price to list construction. The count includes the real linked
callee frame, callee initialization and caller return.
-/

namespace Ram.LanguageCompiler.List.Cons

open Complexity.Language
open Complexity.Language.List.Cons

/-- Return an imported constructor's actual result. The arguments can select
any caller locals; only the existing constructor's three-word allocation is new.
The source execution, arena evidence and exact cost all describe that same call. -/
theorem call_return_ready_cost {kind : CellTy} {signatures : List Signature}
    {target : Complexity.Language.Program signatures}
    {map : SignatureMap [signature kind] signatures}
    (embedded : (program kind).Embeds map target)
    {Γ : List Ty} (args : Args Γ [kind.toTy, .option (.node kind)])
    (initial : Complexity.Language.State Γ) {w heapLimit depth cursor : Nat}
    (positive : 0 < w) (arguments : EnvFits w (args.eval initial.locals))
    (space : cursor + 3 ≤ heapLimit) :
    let inputs := args.eval initial.locals
    let allocated := initial.heap.cons (kind.ofValue inputs.head) inputs.tail.head
    ∃ execution : Complexity.Language.Exec target
        (Complexity.Language.Stmt.callOfEq (map.toFun (entry kind))
          (map.signature_eq (entry kind)) args (.ret (.var .here)))
        initial ⟨initial.locals, allocated.2⟩ (.returned (some allocated.1)),
      ∃ ready : ArenaReady execution w heapLimit (depth + 1) cursor (cursor + 3),
        ArenaExecutionCost ready
          (callCost target (map.toFun (entry kind)) (bodySteps kind + 2) +
            (2 * fieldCount (.option (.node kind)) + 2)) := by
  let inputs := args.eval initial.locals
  let allocated := initial.heap.cons (kind.ofValue inputs.head) inputs.tail.head
  let calleeInitial : Complexity.Language.State [kind.toTy, .option (.node kind)] :=
    initial.enter inputs
  obtain ⟨originalReady, originalCost⟩ := body_ready_cost kind calleeInitial
    (depth := depth) positive (arguments .here) (arguments (.there .here)) space
  obtain ⟨callee, calleeReady, calleeCost⟩ :
      ∃ callee : Complexity.Language.Exec target (map.body target (entry kind))
          calleeInitial ⟨inputs, allocated.2⟩ (.returned (some allocated.1)),
        ∃ ready : ArenaReady callee w heapLimit depth cursor (cursor + 3),
          ArenaExecutionCost ready (bodySteps kind) := by
    rw [embedded (entry kind)]
    exact ⟨(body_exec (program kind) kind calleeInitial).renameCalls embedded,
      originalReady.renameCalls embedded, originalCost.renameCalls embedded⟩
  let received : Complexity.Language.State (.option (.node kind) :: Γ) :=
    Complexity.Language.State.cons (τ := .option (.node kind)) (some allocated.1)
      ⟨initial.locals, allocated.2⟩
  have returnedFits : ValueFits w (τ := .option (.node kind)) (some allocated.1) :=
    ValueFits.option_node positive _
  let returnReady : ArenaReady
      (Complexity.Language.Exec.ret (program := target) (.var .here) received)
      w heapLimit (depth + 1) (cursor + 3) (cursor + 3) :=
    .ret (.var .here) received returnedFits
  refine ⟨Complexity.Language.Exec.callReturnOfEq (map.signature_eq (entry kind))
      callee (Complexity.Language.Exec.ret (.var .here) received),
    ArenaReady.callReturnOfEq (map.signature_eq (entry kind)) arguments
      calleeReady returnReady, ?_⟩
  exact ArenaExecutionCost.callReturnOfEq (map.signature_eq (entry kind))
    (arguments := arguments) calleeCost (.ret (.var .here) received (fits := returnedFits))

end Ram.LanguageCompiler.List.Cons
