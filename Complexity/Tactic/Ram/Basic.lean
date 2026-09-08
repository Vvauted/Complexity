/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Verification.Basic
import Mathlib.Tactic.NormNum

/-!
# Small tactics for RAM verification conditions

* `ram_vc s hs [definitions, facts]` starts an ordinary `Source.Contract`
  proof, naming its entry state and precondition, then performs the mechanical
  weakest-precondition rewrites. `ram_vc [definitions, facts]` performs those
  rewrites on an existing WP goal.
* `ram_simp [definitions, facts]` simplifies expression semantics, state
  updates, heap-read obligations and generated atomic instruction lengths. It
  then invokes mathlib's `norm_num` for arithmetic normalization.

Both tactics are transparent macros over existing proved rules. They neither
unfold `WP` into an execution relation nor expand function calls or loops.
Unknown memory bounds, invariants, arithmetic facts and callee contracts stay
as proof obligations. Extra definitions and facts are unfolded only when the
user supplies them explicitly. The underlying compiler and cost model are
unchanged; the length lemmas below avoid unfolding the complete compiler.
-/

namespace Ram.Tactic

theorem compile_const_length (value : Nat) (dst : Reg) :
    (Expr.compile (.const value) dst).length = 1 := rfl

theorem compile_var_length (r dst : Reg) :
    (Expr.compile (.var r) dst).length = 1 := rfl

theorem compile_bin_length (op : BinOp) (left right : Expr) (dst : Reg) :
    (Expr.compile (.bin op left right) dst).length =
      (left.compile dst).length + (right.compile (dst + 1)).length + 1 := by
  simp only [Expr.compile, List.length_append, List.length_singleton]

theorem compile_load_length (address : Expr) (dst : Reg) :
    (Expr.compile (.load address) dst).length = (address.compile dst).length + 1 := by
  simp only [Expr.compile, List.length_append, List.length_singleton]

theorem stmtSize_assign (n : Nat) (locals : Nat → Nat) (dst : Reg) (value : Expr) :
    LocalCompiler.stmtSize n locals (.assign dst value) =
      (value.compile (ABI.scratch n)).length + 1 := by
  simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
    List.length_append, List.length_singleton]

theorem stmtSize_store (n : Nat) (locals : Nat → Nat) (address value : Expr) :
    LocalCompiler.stmtSize n locals (.store address value) =
      (address.compile (ABI.scratch n)).length +
        (value.compile (ABI.scratch n + 1)).length + 1 := by
  simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
    List.length_append, List.length_singleton]

theorem stmtSize_read (n : Nat) (locals : Nat → Nat) (dst : Reg) :
    LocalCompiler.stmtSize n locals (.read dst) = 1 := rfl

theorem stmtSize_write (n : Nat) (locals : Nat → Nat) (value : Expr) :
    LocalCompiler.stmtSize n locals (.write value) =
      (value.compile (ABI.scratch n)).length + 1 := by
  simp only [LocalCompiler.stmtSize, LocalCompiler.compileStmt,
    List.length_append, List.length_singleton]

end Ram.Tactic

open Lean.Parser.Tactic

/-- Simplify only the RAM expression/state/atomic-length vocabulary and the
explicitly supplied definitions and facts, then normalize numeric arithmetic.
Remaining safety and mathematical obligations are not admitted or hidden. -/
syntax (name := ramSimp) "ram_simp" (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_simp) => `(tactic| ram_simp [])
  | `(tactic| ram_simp [$args,*]) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) only
          [Ram.Tactic.stmtSize_assign, Ram.Tactic.stmtSize_store,
            Ram.Tactic.stmtSize_read, Ram.Tactic.stmtSize_write,
            Ram.Tactic.compile_const_length, Ram.Tactic.compile_var_length,
            Ram.Tactic.compile_bin_length, Ram.Tactic.compile_load_length,
            List.forall_mem_cons, List.forall_mem_nil, List.map_cons, List.map_nil,
            List.length_cons, List.length_nil, and_true, true_and,
            Ram.Expr.ReadsBelow, Ram.Source.State.eval, Ram.Expr.eval, Ram.BinOp.eval,
            Ram.Source.State.setRegs_nil, Ram.Source.State.setRegs_nil_values,
            Ram.Source.State.setRegs_cons,
            Ram.Source.State.setReg, Ram.Source.State.setMem, Ram.Source.State.output,
            BitVec.ofNat_eq_ofNat, $args,*] <;> try norm_num [$args,*] <;> try rfl))

/-- Generate mechanical verification conditions using the proved WP equations.
The two-name form first starts a `Source.Contract` proof. Calls and loops
remain opaque WP obligations to discharge with their explicit contracts. -/
syntax (name := ramVC) "ram_vc" (ppSpace ident ppSpace ident)?
  (" [" simpArg,* "]")? : tactic

macro_rules
  | `(tactic| ram_vc) => `(tactic| ram_vc [])
  | `(tactic| ram_vc [$args,*]) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false }) only
          [Ram.Source.Verification.WP.skip_iff, Ram.Source.Verification.WP.assign_iff,
            Ram.Source.Verification.WP.store_iff, Ram.Source.Verification.WP.read_iff,
            Ram.Source.Verification.WP.write_iff, Ram.Source.Verification.WP.seq_iff,
            Ram.Source.Verification.WP.ite_iff, $args,*] <;> ram_simp [$args,*]))
  | `(tactic| ram_vc $s:ident $hs:ident) => `(tactic| ram_vc $s $hs [])
  | `(tactic| ram_vc $s:ident $hs:ident [$args,*]) =>
      `(tactic|
        (apply Ram.Source.Verification.verify
         intro $s $hs
         ram_vc [$args,*]))
