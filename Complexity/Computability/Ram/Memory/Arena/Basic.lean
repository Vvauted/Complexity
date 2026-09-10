/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Memory.Arena.Registers

/-!
# A word-addressed monotone arena

Address zero holds the shared allocation cursor. The ordinary source program
reserves its interval before initializing it with individual stores. Its two
parameters are length and initial value; its results are base and length.
Only an initialized prefix is represented during the filling loop.
-/

namespace Ram.Source.Arena

/-- One actual initialization store and two cursor assignments. -/
def fillBody : Stmt := Registers.legacy.fillBody

/-- No store is performed when the remaining length is zero. -/
def fill : Stmt := Registers.legacy.fill

/-- Read the shared cursor afresh, reserve the whole interval, then prepare
the traversal. The metadata store precedes every initialization store. -/
def prepare : Stmt := Registers.legacy.prepare

/-- Allocation is existing source IR, without a new heap primitive. -/
def allocate : Stmt := Registers.legacy.allocate

/-- Descriptor results are observed only after initialization has completed. -/
def function : Func where
  params := 2
  locals := 5
  body := allocate
  results := [.var 2, .var 0]

theorem function_wellFormed : function.WellFormed := by
  simp [function, allocate, Func.WellFormed,
    Registers.allocate, Registers.prepare, Registers.fill, Registers.fillBody,
    Registers.legacy, Stmt.WellFormed, Expr.Bounded]

theorem fillBody_isStraightLine : fillBody.IsStraightLine := by
  exact Registers.legacy.fillBody_isStraightLine

theorem prepare_isStraightLine : prepare.IsStraightLine := by
  exact Registers.legacy.prepare_isStraightLine

theorem fillBody_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable fillBody = 11 := rfl

theorem prepare_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable prepare = 12 := rfl

/-- Finite initialized cells, together with the frame outside precisely that
prefix. No property is asserted of the pending, not-yet-written suffix. -/
structure InitializedPrefix (before after : Word w → Word w)
    (base value : Word w) (length : Nat) : Prop where
  initialized : ArrayRep after base (List.replicate length value)
  frame : ArrayFrame base length before after

namespace InitializedPrefix

theorem empty (memory : Word w → Word w) (base value : Word w) :
    InitializedPrefix memory memory base value 0 := by
  refine ⟨⟨?_, ?_⟩, ArrayFrame.refl _ _ _⟩
  · simpa using Nat.le_of_lt base.isLt
  · simp

/-- A single real word update extends exactly the initialized prefix. -/
theorem store {before after : Word w → Word w} {base value : Word w} {length : Nat}
    (initializedPrefix : InitializedPrefix before after base value length)
    (fits : base.toNat + length < 2 ^ w) :
    InitializedPrefix before
      (fun address => if address = arrayAddr base length then value else after address)
      base value (length + 1) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [List.length_replicate]
    omega
  · intro i hi
    have bound : i < length + 1 := by simpa using hi
    by_cases same : i = length
    · subst i
      simp
    · have earlier : i < length := by omega
      have distinct : arrayAddr base i ≠ arrayAddr base length := by
        intro equal
        exact same ((arrayAddr_eq_iff (by omega) fits).mp equal)
      rw [if_neg distinct]
      rw [List.getElem_replicate]
      exact (initializedPrefix.initialized.lookup i (by simpa using earlier)).trans
        (List.getElem_replicate _)
  · intro address outside
    have distinct : address ≠ arrayAddr base length := by
      intro equal
      subst address
      rw [arrayAddr_toNat fits] at outside
      omega
    change (if address = arrayAddr base length then value else after address) = before address
    rw [if_neg distinct]
    exact initializedPrefix.frame address (by omega)

end InitializedPrefix

/-- Sufficient-capacity precondition; allocation does not add an OOM outcome.
The endpoint itself remains a representable cursor word. -/
structure Pre (heapLimit : Nat) (base : Word w) (length : Nat) (value : Word w)
    (entry : State w) : Prop where
  cursor : entry.mem 0 = base
  length_reg : (entry.regs 0).toNat = length
  value_reg : entry.regs 1 = value
  positive : 1 ≤ base.toNat
  capacity : base.toNat + length ≤ heapLimit
  fits : heapLimit < 2 ^ w

/-- Successful allocation exposes initialized contents and the descriptor.
Metadata is the only changed address outside the freshly allocated interval. -/
structure Post (heapLimit : Nat) (base : Word w) (length : Nat) (value : Word w)
    (entry finish : State w) : Prop where
  cursor : finish.mem 0 = arrayAddr base length
  array : ArrayAt heapLimit base (List.replicate length value) finish
  base_reg : finish.regs 2 = base
  length_reg : finish.regs 0 = entry.regs 0
  frame : ∀ address, address ≠ 0 →
    address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
    finish.mem address = entry.mem address
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev
  other : ∀ r, 5 ≤ r → finish.regs r = entry.regs r

end Ram.Source.Arena
