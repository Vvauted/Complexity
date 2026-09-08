/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Analysis.Asymptotics.Polynomial
import Complexity.Computability.Ram.Problem.Basic

/-!
# Bit size of word-list input encodings

Each word occupies exactly its declared width, including leading zero bits.
The bit size below is the packed payload size: it does not add an external
description of the word width or a self-delimiting encoding of the list length.
Headers already present in a problem's input word list are counted.
At width zero this payload size is zero even for a nonempty list; information
carried by its externally supplied length is not counted.

A problem owns its encoding, size measure, and admissible word widths. The
polynomial bound requires word-count and word-width bounds on every input in
that original admissible domain; it does not restrict the domain. Its fixed
coefficient and exponent are uniform in the input and word width.

These are representation-size theorems, not bit-level runtime bounds or a
simulation of unit-cost RAM multiplication and division by a bit machine.
-/

namespace Ram

/-- Number of bits in a list of fixed-width words, retaining leading zeros. -/
def wordListBitSize {w : Nat} (words : List (Word w)) : Nat :=
  w * words.length

@[simp] theorem wordListBitSize_nil (w : Nat) :
    wordListBitSize ([] : List (Word w)) = 0 := by
  simp [wordListBitSize]

@[simp] theorem wordListBitSize_cons {w : Nat} (word : Word w)
    (words : List (Word w)) :
    wordListBitSize (word :: words) = w + wordListBitSize words := by
  simp [wordListBitSize, Nat.mul_add, Nat.add_comm]

@[simp] theorem wordListBitSize_append {w : Nat}
    (left right : List (Word w)) :
    wordListBitSize (left ++ right) =
      wordListBitSize left + wordListBitSize right := by
  simp [wordListBitSize, Nat.mul_add]

/-- Bounds on word count and word width give a bound on packed bit size. -/
theorem wordListBitSize_le {w lengthBound widthBound : Nat}
    (words : List (Word w)) (hlength : words.length ≤ lengthBound)
    (hwidth : w ≤ widthBound) :
    wordListBitSize words ≤ widthBound * lengthBound :=
  Nat.mul_le_mul hwidth hlength

namespace Problem

/-- Packed bit size of exactly the input list published by the problem. -/
def inputBitSize (p : Problem Input) (w : Nat) (input : Input) : Nat :=
  wordListBitSize (p.encode w input)

/-- A pointwise bound; admissibility and the choice of width policy remain
the responsibility of the published problem. -/
theorem inputBitSize_le (p : Problem Input) {w : Nat} {input : Input}
    {lengthBound widthBound : Nat}
    (hlength : (p.encode w input).length ≤ lengthBound)
    (hwidth : w ≤ widthBound) :
    p.inputBitSize w input ≤ widthBound * lengthBound :=
  wordListBitSize_le (p.encode w input) hlength hwidth

/-- Polynomial word-count and word-width bounds give one polynomial bit-size
bound for all of the fixed problem's admissible inputs. This theorem neither
chooses new admissible widths nor supplies a bit-level execution-time bound. -/
theorem inputBitSize_polynomial (p : Problem Input) {L W : Nat → Nat}
    (hL : Asymptotics.IsPolynomiallyBounded L) (hW : Asymptotics.IsPolynomiallyBounded W)
    (hlength : ∀ w input, p.admissible w input →
      (p.encode w input).length ≤ L (p.size input))
    (hwidth : ∀ w input, p.admissible w input → w ≤ W (p.size input)) :
    ∃ c k : Nat, 0 < c ∧ ∀ w input, p.admissible w input →
      p.inputBitSize w input ≤ c * (p.size input + 1) ^ k := by
  obtain ⟨c, k, hc, hbound⟩ := (hW.mul hL).exists_pos
  exact ⟨c, k, hc, fun w input ha =>
    Nat.le_trans (p.inputBitSize_le (hlength w input ha) (hwidth w input ha))
      (hbound (p.size input))⟩

end Problem

end Ram
