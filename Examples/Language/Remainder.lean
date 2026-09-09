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

/-!
# Remainder from mathematical division, multiplication and subtraction

The nested source expression is compiled into actual primitive bindings. Its
result follows from the ordinary Nat division identity, including divisor zero.
All intermediate values fit whenever the two inputs fit; subtraction retains
its saturating Nat meaning. The separate count concerns this division-based
implementation, not the backend's single remainder instruction.
-/

namespace Complexity.Language.Examples.Remainder

open Ram.LanguageCompiler

source_program Implementation where
  def remainder (n : Nat) (d : Nat) : Nat := do
    return n - (n / d) * d

/-- The source implementation has Lean's remainder semantics, also at zero. -/
theorem remainder_eval (n d : Nat) :
    Implementation.remainder n d = Part.some (.ok (n % d)) := by
  rw [Implementation.remainder_eq, Nat.mod_eq_sub_div_mul]
  rfl

/-- An ordinary mathematical specification of the same source function. -/
theorem remainder_total :
    FunctionTotal Implementation.program (0 : Fin 1) (fun _ => True)
      (fun args value => value = Env.head args % Env.head (Env.tail args)) := by
  apply (Implementation.remainder_total_iff (fun _ _ => True)
    (fun n d value => value = n % d)).mpr
  intro n d _
  exact ⟨n % d, remainder_eval n d, rfl⟩

/-- Neither a positive divisor nor a nonnegative machine subtraction premise
is needed. The emitted code implements all mathematical inputs that fit. -/
theorem remainder_realizable {w : Nat} :
    FunctionRealizable Implementation.program w 0 (0 : Fin 1)
      (fun args => Env.head args < 2 ^ w ∧ Env.head (Env.tail args) < 2 ^ w) := by
  apply FunctionRealizable.of_wp
  intro args fits
  change RealizationWP Implementation.program w 0 Implementation.remainderBody
    (fun _ => False) (fun _ _ => True) args
  have quotient := Nat.lt_of_le_of_lt
    (Nat.div_le_self (Env.head args) (Env.head (Env.tail args))) fits.1
  have product := Nat.lt_of_le_of_lt
    (Nat.div_mul_le_self (Env.head args) (Env.head (Env.tail args))) fits.1
  have difference := Nat.lt_of_le_of_lt
    (Nat.sub_le (Env.head args) (Env.head args / Env.head (Env.tail args) *
      Env.head (Env.tail args))) fits.1
  simp only [Implementation.remainderBody,
    RealizationWP.letPrim_iff, RealizationWP.ret_iff, PrimFits, Prim.eval,
    Atom.eval, Env.cons_here, Env.cons_there, valueToNat, and_true]
  exact ⟨fits, ⟨⟨quotient, fits.2, product⟩, ⟨⟨fits.1, product⟩, difference⟩⟩⟩

/-- The exact straight-line body count includes division, multiplication,
saturating subtraction, the return and the function-body wrapper. -/
theorem remainder_costBound :
    FunctionCostBound Implementation.program (0 : Fin 1) (fun _ => True)
      (fun _ => 25) := by
  apply FunctionCostBound.of_stmt (coreBound := fun _ => 20)
  intro args _
  exact StmtCostBound.letPrim _ (StmtCostBound.letPrim _
    (StmtCostBound.letPrim _ (StmtCostBound.ret _ _)))

/-- Generic lowering supplies the actual callable result without a register proof. -/
theorem remainder_functionExec {w heapLimit : Nat} (hw : 0 < w) (n d : Nat)
    (hn : n < 2 ^ w) (hd : d < 2 ^ w) (entry : Ram.Source.State w) :
    ∃ finish, Ram.Source.FunctionExec (lowerProgram Implementation.program) heapLimit 0
      (lowerFunc Implementation.program (0 : Fin 1))
      (envWords w (Env.cons (τ := .nat) n (Env.cons (τ := .nat) d Env.empty))) entry
      (valueWords w (τ := .nat) (n % d)) finish := by
  let args : Env [.nat, .nat] :=
    Env.cons (τ := .nat) n (Env.cons (τ := .nat) d Env.empty)
  have arguments : EnvFits w args := by
    simpa only [args, EnvFits.cons_nat_iff, EnvFits.empty, and_true] using And.intro hn hd
  obtain ⟨value, finish, execution, result⟩ := remainder_realizable.functionExec
    (heapLimit := heapLimit) remainder_total hw args arguments ⟨hn, hd⟩ trivial entry
  have actualValue : (value : Nat) = n % d := result
  exact ⟨finish, actualValue ▸ execution⟩

end Complexity.Language.Examples.Remainder
