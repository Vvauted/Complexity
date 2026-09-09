/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax
import Complexity.Language.Eval.Verification
import Complexity.Computability.Ram.Compiler.Language.Execution
import Complexity.Computability.Ram.Compiler.Language.CostExecution
import Complexity.Computability.Ram.Compiler.Language.CostBound
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Remainder from mathematical division, multiplication and subtraction

The nested source expression is compiled into actual primitive bindings. Its
result follows from the ordinary Nat division identity, including divisor zero.
All intermediate values fit whenever the two inputs fit; subtraction retains
its saturating Nat meaning. The separate count concerns this division-based
implementation, not the backend's single remainder instruction.
Its pure source-action equation also states that every initial heap is preserved.
-/

namespace Complexity.Language.Examples.Remainder

open Ram.LanguageCompiler

source_program Implementation where
  def remainder (n : Nat) (d : Nat) : Nat := do
    return n - (n / d) * d

/-- The source implementation has Lean's remainder semantics, also at zero. -/
theorem remainder_eval (n d : Nat) :
    Implementation.remainder n d =
      (pure (n % d) : ExceptT Fault (StateT Heap Part) Nat) := by
  rw [Implementation.remainder_eq, Nat.mod_eq_sub_div_mul]
  rfl

/-- An ordinary mathematical specification of the same source function. -/
theorem remainder_total :
    FunctionTotal Implementation.program (0 : Fin 1) (fun _ _ => True)
      (fun args heap value finish =>
        value = Env.head args % Env.head (Env.tail args) ∧ finish = heap) := by
  apply (Implementation.remainder_total_iff (fun _ _ _ => True)
    (fun n d heap value finish => value = n % d ∧ finish = heap)).mpr
  intro n d heap _
  exact ⟨n % d, heap, congrFun (remainder_eval n d) heap, rfl, rfl⟩

/-- Neither a positive divisor nor a nonnegative machine subtraction premise
is needed. The emitted code implements all mathematical inputs that fit. -/
theorem remainder_realizable {w : Nat} :
    FunctionRealizable Implementation.program w 0 (0 : Fin 1)
      (fun args _ => Env.head args < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  ram_source_realize (n d)
  all_goals
    have quotient := Nat.div_le_self n d
    have product := Nat.div_mul_le_self n d
    omega

/-- The straight-line body bound includes division, multiplication,
saturating subtraction, the return and the function-body wrapper. -/
theorem remainder_costBound :
    FunctionCostBound Implementation.program (0 : Fin 1) (fun _ _ => True)
      (fun _ _ => 22) := by
  ram_source_cost (n d)

/-- Generic lowering supplies the actual callable result without a register proof. -/
theorem remainder_functionExec {w heapLimit : Nat} (hw : 0 < w) (n d : Nat) (sourceHeap : Heap)
    (hn : n < 2 ^ w) (hd : d < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 0
      (lowerFunc Implementation.program (0 : Fin 1))
      (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) d Env.empty))) entry
      (valueWords w (τ := .nat) (n % d)) finish := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) d Env.empty)
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using And.intro hn hd
  obtain ⟨value, _, finish, _, execution, result⟩ := remainder_realizable.functionExec
    (heapLimit := heapLimit) remainder_total hw args sourceHeap arguments ⟨hn, hd⟩ trivial entry
  have actualValue : (value : Nat) = n % d := result.1
  exact ⟨finish, actualValue ▸ execution⟩

end Complexity.Language.Examples.Remainder
