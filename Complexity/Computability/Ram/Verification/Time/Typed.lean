/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Time.Function
import Complexity.Computability.Ram.Verification.Function.Typed

/-!
# Separate call bounds through typed return values

`FunctionTimeBound.call_seq_typed_at` combines an existing body-time bound
with typed correctness of the same function. Its continuation receives the
actual typed result and shared state, and may bound the remaining work using
either. Argument evaluation, frame handling and all returned fields keep their
compiler-derived costs.

`call_seq_typed_restored_at` exposes restored caller bindings directly in the
continuation state. `call_seq_typed_remaining_at` additionally computes the
continuation's reserve by subtracting the full call bound from the overall
reserve, with an explicit proof that the call is affordable.

This is an adapter to `FunctionTimeBound.call_seq_at`, not a second cost
semantics. The internal additive reserve is only a proof of a time inequality;
it is not execution fuel and is not an argument to the program. The caller
supplies the typed input explicitly, without assuming an inverse argument
decoder or assigning defaults to malformed return lists.
-/

namespace Ram.Source.FunctionTimeBound

/-- Compose a call with a typed result-dependent continuation bound. Correctness
and time remain separate properties of the same invocation. The continuation
starts after the actual ordered destination updates, including an empty return. -/
theorem call_seq_typed_at {α : Type*} {w control heapLimit depth : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind}
    {encodeArgs : α → List (Word w)} {P : α → State w → Prop}
    {Q : α → State w → kind.Value w → State w → Prop}
    {R : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f R bound)
    (correct : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (arg : α) {fn : Nat} {dsts : List Reg} {args : List Expr}
    {tail : Stmt} {entry : State w} {overall : Nat}
    (lookup : program[fn]? = some f)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (argumentValues : args.map entry.eval = encodeArgs arg)
    (pre : P arg entry) (timePre : R (encodeArgs arg) entry)
    (nextBound : kind.Value w → State w → Nat)
    (continuation : ∀ value finish, Q arg entry value finish →
      finish.regs = entry.regs →
      TimeBound control program heapLimit (depth + 1) tail
        (fun s => s = finish.setRegs dsts (kind.encode value))
        (fun _ => nextBound value finish))
    (budget : ∀ value finish, Q arg entry value finish →
      finish.regs = entry.regs →
      (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bound (encodeArgs arg) entry +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length +
        nextBound value finish ≤ overall) :
    TimeBound control program heapLimit (depth + 1) (.seq (.call dsts fn args) tail)
      (fun s => s = entry) (fun _ => overall) := by
  let callPre : List (Word w) → State w → Prop :=
    fun values state => values = encodeArgs arg ∧ state = entry
  have rawCorrect : FunctionContract program heapLimit depth f callPre
      (fun _ state fields finish =>
        ∃ value, fields = kind.encode value ∧ Q arg state value finish) :=
    (correct.raw arg).consequence
      (by rintro values state ⟨rfl, rfl⟩; exact ⟨rfl, pre⟩)
      (by intro values state fields finish _ post; exact post)
  have rawTime : FunctionTimeBound control program heapLimit depth f callPre bound := by
    rintro values state ⟨rfl, rfl⟩ steps fields finish execution
    exact time _ _ timePre steps fields finish execution
  let callCost := (ABI.callPrefixLocals control f.locals args 0).length + 1 +
    bound (encodeArgs arg) entry +
    (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length
  have callLe : callCost ≤ overall := by
    obtain ⟨value, finish, invocation, post⟩ := correct arg entry pre
    have bounded := budget value finish post invocation.regs_eq
    change callCost + nextBound value finish ≤ overall at bounded
    omega
  apply rawTime.call_seq_at rawCorrect lookup arguments
    (show callPre (args.map entry.eval) entry from ⟨argumentValues, rfl⟩)
    (nextBound := fun _ _ => overall - callCost)
  · rintro fields finish ⟨value, rfl, post⟩ locals
    apply (continuation value finish post locals).mono_budget
    intro state _
    have bounded := budget value finish post locals
    change callCost + nextBound value finish ≤ overall at bounded
    omega
  · intro fields finish _ _
    rw [argumentValues]
    change callCost + (overall - callCost) ≤ overall
    omega

/-- Compose a typed call with its actual shared effects and restored caller
bindings visible in the continuation state. The continuation bound may still
depend on the returned value and restored state, without a separate register
equality to carry through later calls. -/
theorem call_seq_typed_restored_at {α : Type*} {w control heapLimit depth : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind}
    {encodeArgs : α → List (Word w)} {P : α → State w → Prop}
    {Q : α → State w → kind.Value w → State w → Prop}
    {R : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f R bound)
    (correct : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (arg : α) {fn : Nat} {dsts : List Reg} {args : List Expr}
    {tail : Stmt} {entry : State w} {overall : Nat}
    (lookup : program[fn]? = some f)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (argumentValues : args.map entry.eval = encodeArgs arg)
    (pre : P arg entry) (timePre : R (encodeArgs arg) entry)
    (nextBound : kind.Value w → State w → Nat)
    (continuation : ∀ value shared, Q arg entry value (entry.restore shared) →
      TimeBound control program heapLimit (depth + 1) tail
        (fun s => s = (entry.restore shared).setRegs dsts (kind.encode value))
        (fun _ => nextBound value (entry.restore shared)))
    (budget : ∀ value shared, Q arg entry value (entry.restore shared) →
      (ABI.callPrefixLocals control f.locals args 0).length + 1 +
        bound (encodeArgs arg) entry +
        (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length +
        nextBound value (entry.restore shared) ≤ overall) :
    TimeBound control program heapLimit (depth + 1) (.seq (.call dsts fn args) tail)
      (fun s => s = entry) (fun _ => overall) := by
  have restore_eq (finish : State w) (registers : finish.regs = entry.regs) :
      entry.restore finish = finish := by
    unfold State.restore
    rw [← registers]
  apply time.call_seq_typed_at correct arg lookup arguments argumentValues pre timePre nextBound
  · intro value finish result registers
    have restored := restore_eq finish registers
    simpa only [restored] using
      continuation value finish (by simpa only [restored] using result)
  · intro value finish result registers
    have restored := restore_eq finish registers
    simpa only [restored] using
      budget value finish (by simpa only [restored] using result)

/-- Use the overall reserve left after the compiler-derived call overhead and
callee body bound for the continuation. Affordability justifies natural
subtraction; it is not execution fuel or a monotonicity assumption on time bounds.
The continuation still receives the actual typed result and shared effects. -/
theorem call_seq_typed_remaining_at {α : Type*} {w control heapLimit depth : Nat}
    {program : Program} {f : Func} {kind : DSL.ValueKind}
    {encodeArgs : α → List (Word w)} {P : α → State w → Prop}
    {Q : α → State w → kind.Value w → State w → Prop}
    {R : List (Word w) → State w → Prop} {bound : List (Word w) → State w → Nat}
    (time : FunctionTimeBound control program heapLimit depth f R bound)
    (correct : TypedFunctionContract program heapLimit depth f kind encodeArgs P Q)
    (arg : α) {fn : Nat} {dsts : List Reg} {args : List Expr}
    {tail : Stmt} {entry : State w} {overall : Nat}
    (lookup : program[fn]? = some f)
    (arguments : ∀ expr ∈ args, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (argumentValues : args.map entry.eval = encodeArgs arg)
    (pre : P arg entry) (timePre : R (encodeArgs arg) entry)
    (affordable : (ABI.callPrefixLocals control f.locals args 0).length + 1 +
      bound (encodeArgs arg) entry +
      (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length ≤ overall)
    (continuation : ∀ value shared, Q arg entry value (entry.restore shared) →
      TimeBound control program heapLimit (depth + 1) tail
        (fun s => s = (entry.restore shared).setRegs dsts (kind.encode value))
        (fun _ => overall - ((ABI.callPrefixLocals control f.locals args 0).length + 1 +
          bound (encodeArgs arg) entry +
          (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length))) :
    TimeBound control program heapLimit (depth + 1) (.seq (.call dsts fn args) tail)
      (fun s => s = entry) (fun _ => overall) := by
  apply time.call_seq_typed_restored_at correct arg lookup arguments argumentValues pre timePre
    (fun _ _ => overall - ((ABI.callPrefixLocals control f.locals args 0).length + 1 +
      bound (encodeArgs arg) entry +
      (ABI.returnCodeResultsLocals control f.locals f.results).length + dsts.length))
  · exact continuation
  · intro value shared result
    omega

end Ram.Source.FunctionTimeBound
