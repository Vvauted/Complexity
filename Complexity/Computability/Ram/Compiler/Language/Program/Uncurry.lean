/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Measured.Call
import Complexity.Computability.Ram.Compiler.Language.Arena.CostBound.Call

/-!
# Executable unpacking of a binary source call

A source entry accepting one product can project its two fields and invoke an
existing binary function. This structural wrapper is real source code, not a
host conversion or a replacement implementation of the callee. The shared
measured and cost bridges retain the original callee's actual heap, value and
cursor through a checked program embedding.

Both field projections, the actual call, and the final return keep their
existing compiler charges. The wrapper needs one additional call level but no
additional heap allocation. Its own function initialization, when made an entry
body, remains the responsibility of the ordinary function-body bridge.
-/

namespace Complexity.Program.Uncurry

open Language Ram.LanguageCompiler

/-- The actual two-parameter environment obtained by projecting a product. -/
def arguments {left right : Ty} (value : Value (.prod left right)) : Env [left, right] :=
  Env.cons value.1 (Env.cons value.2 Env.empty)

/-- Project both fields, call the selected binary source function, and return
its actual result. There is no callee-body duplication or new program table. -/
def call {signatures : List Signature} {left right result : Ty}
    (fn : Fin signatures.length) (same : signatures[fn] = ⟨[left, right], result⟩) :
    Language.Stmt signatures [.prod left right] result :=
  .letPrim (.fst (.var .here))
    (.letPrim (.snd (.var (.there .here)))
      (.callOfEq fn same
        (.cons (.var (.there .here)) (.cons (.var .here) .nil))
        (.ret (.var .here))))

/-- The field-copy count supplied by the existing primitive lowering for the
two actual projections; no operation on the contents of either field occurs. -/
def projectionCost (left right : Ty) : Nat :=
  2 * fieldCount left + 2 * fieldCount right

/-- The existing compiler charges for unpacking, calling and returning. The
callee budget already includes its initialization; this wrapper's own function
initialization is not part of its statement-core envelope. -/
def callBound {signatures : List Signature} (program : Language.Program signatures)
    (fn : Fin signatures.length) (left right : Ty) (calleeBodyBound : Nat) : Nat :=
  projectionCost left right + callCost program fn calleeBodyBound +
    (2 * fieldCount signatures[fn].result + 2)

/-- The structural wrapper adds only fixed compiler-derived overhead to the
selected callee's body budget, with no input-dependent ABI assumption. -/
theorem callBound_eq {signatures : List Signature} (program : Language.Program signatures)
    (fn : Fin signatures.length) (left right : Ty) (calleeBodyBound : Nat) :
    callBound program fn left right calleeBodyBound =
      calleeBodyBound + callBound program fn left right 0 := by
  unfold callBound
  rw [callCost_eq_add program fn calleeBodyBound]
  omega

/-- Invoke an existing imported measured binary body through a real product
entry. The returned value, final heap and cursor are those of the same callee;
its core count is retained alongside the complete wrapper core count. -/
theorem call_measured_imported
    {source target : List Signature}
    {sourceProgram : Language.Program source} {targetProgram : Language.Program target}
    {map : SignatureMap source target} (embedded : sourceProgram.Embeds map targetProgram)
    {left right result : Ty} (fn : Fin source.length)
    (same : source[fn] = ⟨[left, right], result⟩)
    {w heapLimit depth cursor : Nat} (entry : Language.State [.prod left right])
    (fits : ValueFits w entry.locals.head)
    {P : Heap → Value result → Nat → Nat → Prop}
    (callee : ArenaMeasured sourceProgram w heapLimit depth
      (cast (congrArg (fun s => Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn))
      (fun finish control finalCursor steps =>
        ∃ value, control = .returned value ∧ P finish.heap value finalCursor steps)
      ⟨arguments entry.locals.head, entry.heap⟩ cursor) :
    ArenaMeasured targetProgram w heapLimit (depth + 1)
      (call (map.toFun fn) ((map.signature_eq fn).trans same))
      (fun finish control finalCursor steps => ∃ value calleeSteps,
        control = .returned value ∧ P finish.heap value finalCursor calleeSteps ∧
          steps = projectionCost left right +
            callCost targetProgram (map.toFun fn) (calleeSteps + 2) +
              (2 * fieldCount result + 2)) entry cursor := by
  unfold call
  apply ArenaMeasured.letPrim
  · exact fits
  · apply ArenaMeasured.letPrim
    · exact fits
    · apply ArenaMeasured.call_measured_imported embedded same
        (args := .cons (.var (.there .here)) (.cons (.var .here) .nil))
        (continuation := .ret (.var .here))
      · exact EnvFits.cons (EnvFits.cons (EnvFits.empty w) _ fits.2) _ fits.1
      · exact callee
      · intro finish value finalCursor steps property valueFits
        apply ArenaMeasured.ret
        · exact valueFits
        · exact ⟨value, steps, rfl, property, by
            simp only [projectionCost, primCodeSize, Nat.add_assoc]⟩

/-- Reuse an indexed bound for the actual imported binary body. Costs remain
conditional on the given execution, independently of ranges and termination;
the two projections and the actual result return are included explicitly. -/
theorem call_costBound_imported {X : Type*}
    {source target : List Signature}
    {sourceProgram : Language.Program source} {targetProgram : Language.Program target}
    {map : SignatureMap source target} (embedded : sourceProgram.Embeds map targetProgram)
    {left right result : Ty} (fn : Fin source.length)
    (same : source[fn] = ⟨[left, right], result⟩)
    {w heapLimit depth : Nat} {calleeArgs : X → Env [left, right]}
    {pre : X → Heap → Prop} {bound : X → Nat}
    (callee : FunctionArenaCostBound sourceProgram
      (cast (congrArg (fun s => Language.Stmt source s.params s.result) same)
        (sourceProgram.body fn)) calleeArgs pre w heapLimit depth bound)
    (entry : Language.State [.prod left right]) (x : X)
    (arguments_eq : calleeArgs x = arguments entry.locals.head)
    (allowed : pre x entry.heap) :
    StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (call (map.toFun fn) ((map.signature_eq fn).trans same)) entry
      (projectionCost left right + callCost targetProgram (map.toFun fn) (bound x) +
        (2 * fieldCount result + 2)) := by
  have relocated := callee.renameCalls embedded
  rw [Language.Stmt.renameCalls_cast map same, ← embedded fn] at relocated
  have linked : FunctionArenaCostBound targetProgram
      (cast (congrArg (fun s => Language.Stmt target s.params s.result)
        ((map.signature_eq fn).trans same)) (targetProgram.body (map.toFun fn)))
      calleeArgs pre w heapLimit depth bound := by
    simpa only [SignatureMap.body, cast_cast] using relocated
  have bounded : StmtArenaCostBound targetProgram w heapLimit (depth + 1)
      (call (map.toFun fn) ((map.signature_eq fn).trans same)) entry
      (2 * fieldCount left + (2 * fieldCount right +
        (callCost targetProgram (map.toFun fn) (bound x) + (2 * fieldCount result + 2)))) := by
    unfold call
    apply StmtArenaCostBound.letPrim
    apply StmtArenaCostBound.letPrim
    apply StmtArenaCostBound.call_at_of_eq ((map.signature_eq fn).trans same) linked x
    · exact arguments_eq
    · exact allowed
    · intro value heap
      intro finish control execution cursor finalCursor ready steps counted
      exact StmtArenaCostBound.ret (.var .here) _ execution ready counted
  intro finish control execution cursor finalCursor ready steps counted
  simpa only [projectionCost, Nat.add_assoc] using bounded execution ready counted

end Complexity.Program.Uncurry
