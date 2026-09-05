import Ram.ABI

/-!
# Length identities for generated call code

These are equations about the compiler's concrete instruction lists, not an
operation-price table. The call execution proof supplies the counted execution
to which the last identity applies. In particular, saving and restoring `n`
locals contributes the lengths of their individual stores and loads.
-/

namespace Ram.ABI

theorem evalArgs_length (n : Nat) (args : List Expr) (start : Nat) :
    (evalArgs n start args).length =
      (args.map (fun e => (e.compile (scratch n)).length)).sum + args.length := by
  induction args generalizing start with
  | nil => rfl
  | cons e es ih =>
      simp only [evalArgs, List.length_append, ih,
        List.map_cons, List.sum_cons, List.length_cons, List.length_nil]
      omega

theorem callPrefix_length_eq (n : Nat) (args : List Expr) (returnPC : Nat) :
    (callPrefix n args returnPC).length =
      (args.map (fun e => (e.compile (scratch n)).length)).sum + args.length + 4 * n + 4 := by
  simp only [callPrefix, List.length_append, evalArgs_length, saveReturn,
    List.length_cons, List.length_nil, saveLocals_length, initLocals_length, advance]
  omega

theorem returnPrefix_length (n : Nat) (result : Expr) :
    (returnPrefix n result).length = (result.compile (scratch n)).length + 3 * n + 4 := by
  simp only [returnPrefix, List.length_append, List.length_cons, List.length_nil,
    retreat, restoreLocals_length]
  omega

theorem returnCode_length (n : Nat) (result : Expr) :
    (returnCode n result).length = (result.compile (scratch n)).length + 3 * n + 5 := by
  simp only [returnCode, List.length_append, List.length_singleton, returnPrefix_length]

/-- Simplify the exact count assembled from setup, entry jump, body, return
code, and receive. The body count is supplied by its real execution theorem. -/
theorem call_steps_eq (n : Nat) (args : List Expr) (result : Expr)
    (returnPC bodySteps : Nat) :
    (callPrefix n args returnPC).length + 1 + bodySteps + (returnCode n result).length + 1 =
      (args.map (fun e => (e.compile (scratch n)).length)).sum + bodySteps +
        (result.compile (scratch n)).length + 7 * n + args.length + 11 := by
  rw [callPrefix_length_eq, returnCode_length]
  omega

end Ram.ABI
