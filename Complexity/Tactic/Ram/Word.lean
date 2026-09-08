/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Word
import Mathlib.Tactic.NormNum

/-!
# Focused unsigned-word arithmetic

`ram_word [facts]` translates unsigned word arithmetic and comparisons to `Nat`.
It first tries the existing no-overflow lemmas using the local hypotheses, then
falls back to the exact modular equations. In particular, subtraction without
an ordering proof is **not** replaced by truncated natural subtraction.

The optional location has the usual simplifier meaning: `ram_word at h` changes
the hypothesis, and `ram_word at *` also normalizes the context. The tactic is a
transparent composition of `simp only`, `norm_num`, and `omega`; it does not
unfold programs or perform unrestricted proof search. Unsatisfied arithmetic
conditions remain visible in the resulting goal. Width zero and division by
zero retain the semantics of `Ram.Word`.

The `↓` rules run before modular expansion, including when another rewrite
exposes a nested operation. This makes the preference for proved exact
arithmetic explicit instead of relying on simp-lemma insertion order. The
final `omega` step is not a general nonlinear-arithmetic solver.
-/

open Lean.Parser.Tactic

/-- Normalize unsigned word arithmetic, using proved no-wrap conditions when
available and exact modular semantics otherwise. Additional facts are explicit
simp arguments; no arithmetic precondition is assumed by the tactic. -/
syntax (name := ramWord) "ram_word" (" [" simpArg,* "]")? (location)? : tactic

macro_rules
  | `(tactic| ram_word $[$loc:location]?) => `(tactic| ram_word [] $[$loc]?)
  | `(tactic| ram_word [$args,*] $[$loc:location]?) =>
      `(tactic|
        (simp (config := { failIfUnchanged := false })
          (disch := omega) only
          [Ram.BinOp.eval_eq_ne_zero_iff, Ram.BinOp.eval_ult_ne_zero_iff,
            Ram.BinOp.eval_ule_ne_zero_iff, Ram.BinOp.eval_eq_toNat,
            Ram.BinOp.eval_ult_toNat, Ram.BinOp.eval_ule_toNat, $args,*] $[$loc]?
         <;> simp (config := { failIfUnchanged := false }) only
          [Ram.BinOp.eval_add, Ram.BinOp.eval_sub, Ram.BinOp.eval_mul,
            Ram.BinOp.eval_udiv, Ram.BinOp.eval_umod, Ram.BinOp.eval_eq,
            Ram.BinOp.eval_ult, Ram.BinOp.eval_ule, BitVec.toNat_eq,
            BitVec.toNat_ne, BitVec.le_def, BitVec.lt_def, apply_ite, $args,*] $[$loc]?
         <;> simp (config := { failIfUnchanged := false })
          (disch := omega) only
          [↓BitVec.toNat_add_of_lt, ↓BitVec.toNat_sub_of_le,
            ↓BitVec.toNat_sub_of_lt,
            ↓BitVec.toNat_mul_of_lt, ↓BitVec.toNat_one,
            ↓Ram.Word.ofNat_toNat_of_lt,
            BitVec.toNat_add, BitVec.toNat_sub', BitVec.toNat_mul,
            BitVec.toNat_udiv, BitVec.toNat_umod, BitVec.ofNat_eq_ofNat,
            BitVec.toNat_ofNat, BitVec.toNat_zero, $args,*] $[$loc]?
         <;> simp (config := { failIfUnchanged := false })
          (disch := omega) only
          [Nat.mod_eq_of_lt, $args,*] $[$loc]?
         <;> try norm_num only [] $[$loc]?
         <;> try omega))

namespace Ram.BinOp

/-- Replacing part of a word by a no-larger offset stays within the word range.
This packages the two intermediate no-wrap obligations of the common
subtract-then-add address calculation. -/
theorem eval_sub_add_toNat (x y z : Word w)
    (hy : y.toNat ≤ x.toNat) (hz : z.toNat ≤ y.toNat) :
    (eval .add (eval .sub x y) z).toNat = x.toNat - y.toNat + z.toNat := by
  have hx := x.isLt
  ram_word [hy, hz]

/-- A bound on the complete multiply-add expression also discharges the
intermediate product bound; callers need not provide both separately. -/
theorem eval_mul_add_toNat_of_lt (x y z : Word w)
    (h : x.toNat * y.toNat + z.toNat < 2 ^ w) :
    (eval .add (eval .mul x y) z).toNat = x.toNat * y.toNat + z.toNat := by
  ram_word at *

/-- A nonzero unsigned comparison after a non-underflowing subtraction is an
ordinary bound on the original operands. -/
theorem eval_sub_ult_ne_zero_iff (hw : 0 < w) (x y z : Word w)
    (hy : y.toNat ≤ x.toNat) :
    eval .ult (eval .sub x y) z ≠ 0 ↔ x.toNat < y.toNat + z.toNat := by
  ram_word

end Ram.BinOp
