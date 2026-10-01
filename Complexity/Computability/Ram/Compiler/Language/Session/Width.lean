/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeBound

/-!
# Word width for external scales and finite request histories

A protocol-fixed raw word presentation extends the configuration's usual logarithmic
scale with the raw request values and their total word count. This list is proof-side
machine admission data, not a source input, an initial heap or preprocessing.
It is chosen by the interface author, before the candidate; it must not contain
computed answers or candidate-selected padding.

At a fixed configuration and width, the initial source and machine memory are
exactly the existing configuration realization, independently of the history.
Only the actual current request reaches a callback. The source language cannot
inspect this width policy. Requiring every sufficiently large width avoids
selecting a special width to encode advice. This is a finite word-RAM convention,
not a dynamically growing-word implementation for an infinite stream.
-/

namespace Complexity.Language.Session

universe u v

variable {α : Type u} [Complexity.Program.Input α] [Complexity.Program.RamInput α]
variable {ι : Type v}

/-- Extend configuration admission with protocol-fixed raw scale words. These
words are proof data, not additional initializer arguments or heap contents.
They may describe an external size unknown to the source; the source semantics
cannot inspect the word width. The protocol fixes them before the candidate. -/
def widthWith (overhead : Nat) (x : α) (words : Array Nat) : Nat :=
  ArrayFunction.width overhead (Complexity.Program.RamInput.words x ++ words)

/-- Additional admission words retain the existing configuration-arena bound. -/
theorem widthWith_base {overhead w : Nat} {x : α} {words : Array Nat}
    (admitted : widthWith overhead x words ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
      (Complexity.Program.RamInput.words x) ≤ w := by
  have configBound := Ram.LanguageCompiler.ArrayFunction.inputWordWidth_append_left
    (Complexity.Program.RamInput.words x) words
  exact (Nat.add_le_add_left configBound 1).trans
    ((ArrayFunction.width_base overhead
      (Complexity.Program.RamInput.words x ++ words)).trans admitted)

/-- At a fixed configuration and width, external scale data does not change
any initial memory. Different admission proofs are not runtime inputs. -/
theorem ofInput_widthWith_independent {overhead₁ overhead₂ w : Nat}
    {x : α} {words₁ words₂ : Array Nat}
    (first : widthWith overhead₁ x words₁ ≤ w)
    (second : widthWith overhead₂ x words₂ ≤ w) :
    Ram.LanguageCompiler.Session.State.ofInput x w (widthWith_base first) =
      Ram.LanguageCompiler.Session.State.ofInput x w (widthWith_base second) := rfl

/-- Raw configuration and request words used only to fix the machine-width scale.
The source initial memory continues to contain only the configuration. -/
def historyWords (requestWords : ι → Array Nat) (x : α) (inputs : List ι) : Array Nat :=
  Complexity.Program.RamInput.words x ++
    (inputs.flatMap fun input => (requestWords input).toList).toArray

/-- The same global multiplier and logarithmic scale as the existing program
policy, now covering a finite history's public scalar values as well. -/
def historyWidth (overhead : Nat) (requestWords : ι → Array Nat)
    (x : α) (inputs : List ι) : Nat :=
  ArrayFunction.width overhead (historyWords requestWords x inputs)

/-- History admission implies the existing configuration-arena admission. -/
theorem historyWidth_base {overhead w : Nat} {requestWords : ι → Array Nat}
    {x : α} {inputs : List ι}
    (admitted : historyWidth overhead requestWords x inputs ≤ w) :
    1 + Ram.LanguageCompiler.ArrayFunction.inputWordWidth
      (Complexity.Program.RamInput.words x) ≤ w :=
  widthWith_base (words := (inputs.flatMap fun input => (requestWords input).toList).toArray)
    admitted

/-- Every finite history has an admitted width for every fixed multiplier. -/
theorem exists_historyWidth (overhead : Nat) (requestWords : ι → Array Nat)
    (x : α) (inputs : List ι) :
    ∃ w, historyWidth overhead requestWords x inputs ≤ w :=
  ⟨historyWidth overhead requestWords x inputs, Nat.le_refl _⟩

/-- At fixed configuration and machine width, the complete initialized memory
does not depend on which future history justified that width. -/
theorem ofInput_history_independent {overhead₁ overhead₂ w : Nat}
    {requestWords : ι → Array Nat} {x : α} {inputs₁ inputs₂ : List ι}
    (first : historyWidth overhead₁ requestWords x inputs₁ ≤ w)
    (second : historyWidth overhead₂ requestWords x inputs₂ ≤ w) :
    Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base first) =
      Ram.LanguageCompiler.Session.State.ofInput x w (historyWidth_base second) := rfl

end Complexity.Language.Session
