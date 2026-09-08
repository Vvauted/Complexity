/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Expr.Basic
import Init.Data.List.Lemmas

/-!
# Contiguous arrays represented in word-addressed memory

An array is a sequence of individual heap words, not a new machine operation.
`ArrayRep` is a specification assertion: its `List` describes the logical
contents and is never inserted into a RAM instruction. Bounds guarantee that
address arithmetic does not wrap and that distinct elements do not alias.

The update theorems refer to the same single-word update used by `State.setMem`
and the `store` instruction. The expression theorem connects source indexing
to the existing verified compiler. Execution counts remain derived from the
generated code and the machine's transition relation.
-/

namespace Ram

/-- The address calculated by ordinary word addition for element `i`. -/
def arrayAddr (base : Word w) (i : Nat) : Word w :=
  base + BitVec.ofNat w i

/-- A non-wrapping address has precisely its mathematical offset. -/
theorem arrayAddr_toNat {base : Word w} {i : Nat}
    (hfit : base.toNat + i < 2 ^ w) :
    (arrayAddr base i).toNat = base.toNat + i := by
  have hi : i < 2 ^ w := by omega
  rw [arrayAddr, BitVec.toNat_add, Word.ofNat_toNat_of_lt hi, Nat.mod_eq_of_lt hfit]

/-- Two non-wrapping offsets identify the same address exactly when they agree. -/
theorem arrayAddr_eq_iff {base : Word w} {i j : Nat}
    (hi : base.toNat + i < 2 ^ w) (hj : base.toNat + j < 2 ^ w) :
    arrayAddr base i = arrayAddr base j ↔ i = j := by
  constructor
  · intro h
    have he := congrArg (fun x : Word w => x.toNat) h
    change (arrayAddr base i).toNat = (arrayAddr base j).toNat at he
    rw [arrayAddr_toNat hi, arrayAddr_toNat hj] at he
    omega
  · rintro rfl
    rfl

/-- A contiguous, non-wrapping array in the mathematical view of RAM memory.
No ownership of memory outside this interval is asserted. -/
structure ArrayRep (mem : Word w → Word w) (base : Word w)
    (xs : List (Word w)) : Prop where
  fits : base.toNat + xs.length ≤ 2 ^ w
  lookup : ∀ (i : Nat) (hi : i < xs.length), mem (arrayAddr base i) = xs[i]

namespace ArrayRep

/-- Every valid element address can be interpreted without modular reduction. -/
theorem addr_toNat {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i : Nat} (hi : i < xs.length) :
    (arrayAddr base i).toNat = base.toNat + i := by
  apply arrayAddr_toNat
  have hfit := hrep.fits
  omega

/-- Valid elements occupy pairwise distinct machine addresses. -/
theorem addr_eq_iff {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    arrayAddr base i = arrayAddr base j ↔ i = j := by
  apply arrayAddr_eq_iff <;> have hfit := hrep.fits <;> omega

/-- A raw heap read using the source language's address expression is the
specified list element. The offset is encoded as a word, not passed to a
host-language array primitive. -/
theorem read {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i : Nat} (hi : i < xs.length) :
    mem (base + BitVec.ofNat w i) = xs[i] := hrep.lookup i hi

/-- Updating one represented element preserves the complete array assertion,
with exactly that position changed in its logical contents. -/
theorem store {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i : Nat} (hi : i < xs.length) (value : Word w) :
    ArrayRep (fun a => if a = arrayAddr base i then value else mem a)
      base (xs.set i value) := by
  refine ⟨by simpa using hrep.fits, ?_⟩
  intro j hj
  have hj' : j < xs.length := by simpa using hj
  change (if arrayAddr base j = arrayAddr base i then value else mem (arrayAddr base j)) =
    (xs.set i value)[j]
  by_cases hij : i = j
  · subst j
    simp
  · have haddr : arrayAddr base j ≠ arrayAddr base i := by
      intro he
      exact hij ((hrep.addr_eq_iff hj' hi).mp he).symm
    rw [if_neg haddr, List.getElem_set_ne hij]
    exact hrep.lookup j hj'

/-- The target element reads back the word just stored. -/
theorem store_read_same (mem : Word w → Word w) (base : Word w)
    (i : Nat) (value : Word w) :
    (fun a => if a = arrayAddr base i then value else mem a) (arrayAddr base i) =
      value := by
  simp

/-- A store to another valid element leaves this element unchanged. -/
theorem store_read_ne {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (hij : i ≠ j) (value : Word w) :
    (fun a => if a = arrayAddr base i then value else mem a) (arrayAddr base j) =
      xs[j] := by
  have haddr : arrayAddr base j ≠ arrayAddr base i := by
    intro he
    exact hij ((hrep.addr_eq_iff hj hi).mp he).symm
  simp only [if_neg haddr]
  exact hrep.lookup j hj

/-- A store outside the represented interval leaves the entire array intact. -/
theorem store_outside {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) (addr value : Word w)
    (hout : addr.toNat < base.toNat ∨ base.toNat + xs.length ≤ addr.toNat) :
    ArrayRep (fun a => if a = addr then value else mem a) base xs := by
  refine ⟨hrep.fits, ?_⟩
  intro i hi
  have haddr : arrayAddr base i ≠ addr := by
    intro he
    have hn := congrArg (fun x : Word w => x.toNat) he
    change (arrayAddr base i).toNat = addr.toNat at hn
    rw [hrep.addr_toNat hi] at hn
    omega
  simp only [if_neg haddr]
  exact hrep.lookup i hi

/-- The array update assertion applies directly to the machine state's
existing single-word memory update. -/
theorem setMem {s : State w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep s.mem base xs) {i : Nat} (hi : i < xs.length) (value : Word w) :
    ArrayRep (s.setMem (arrayAddr base i) value).mem base (xs.set i value) :=
  hrep.store hi value

/-- Executing the actual store instruction changes exactly the selected
logical element. Its address must be present in the address register. -/
theorem exec_store {s : State w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep s.mem base xs) {i : Nat} (hi : i < xs.length)
    (addrReg src : Reg) (haddr : s.regs addrReg = arrayAddr base i) :
    ArrayRep (execInstr (.store addrReg src) s).mem base (xs.set i (s.regs src)) := by
  simpa only [execInstr, State.next_mem, haddr] using hrep.setMem hi (s.regs src)

/-- A fetched store is a real machine transition preserving the updated array
assertion and the register file. No separate source cost is introduced. -/
theorem step_store {code : Code} {s : State w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep s.mem base xs) {i : Nat} (hi : i < xs.length)
    (addrReg src : Reg) (haddr : s.regs addrReg = arrayAddr base i)
    (hrun : s.status = .running) (hfetch : code[s.pc]? = some (.store addrReg src)) :
    ∃ t, step code s = some t ∧ ArrayRep t.mem base (xs.set i (s.regs src)) ∧
      t.regs = s.regs := by
  exact ⟨execInstr (.store addrReg src) s, step_of_fetch hrun hfetch,
    hrep.exec_store hi addrReg src haddr, rfl⟩

/-- Source indexing has the array's mathematical meaning whenever its base
and offset expressions evaluate to the required address components. -/
theorem eval_index {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) (regs : Reg → Word w) (b offset : Expr)
    {i : Nat} (hi : i < xs.length) (hb : b.eval regs mem = base)
    (hoffset : offset.eval regs mem = BitVec.ofNat w i) :
    (Expr.index b offset).eval regs mem = xs[i] := by
  rw [Expr.eval_index, hb, hoffset]
  exact hrep.read hi

/-- The verified expression compiler actually computes the represented array
element. Its standard source-register bound prevents scratch-register clashes. -/
theorem compiled_index {s : State w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep s.mem base xs) (b offset : Expr) (dst : Reg)
    (hbnd : b.Bounded dst) (hobnd : offset.Bounded dst)
    {i : Nat} (hi : i < xs.length) (hb : b.eval s.regs s.mem = base)
    (hoffset : offset.eval s.regs s.mem = BitVec.ofNat w i) :
    (execBlock ((Expr.index b offset).compile dst) s).regs dst = xs[i] := by
  rw [(Expr.compile_correct (e := Expr.index b offset) ⟨hbnd, hobnd⟩ s).value]
  exact hrep.eval_index s.regs b offset hi hb hoffset

/-- Array indexing refines to an execution of the generated RAM block, with
its transition count inherited from the compiler theorem. -/
theorem compiled_index_exec {code : Code} {s : State w} {base : Word w}
    {xs : List (Word w)} (hrep : ArrayRep s.mem base xs)
    (b offset : Expr) (dst : Reg) (hbnd : b.Bounded dst) (hobnd : offset.Bounded dst)
    {i : Nat} (hi : i < xs.length) (hb : b.eval s.regs s.mem = base)
    (hoffset : offset.eval s.regs s.mem = BitVec.ofNat w i)
    (hcode : CodeAt code s.pc ((Expr.index b offset).compile dst))
    (hrun : s.status = .running) :
    ∃ t, Exec code ((Expr.index b offset).compile dst).length s t ∧
      t.regs dst = xs[i] ∧ t.mem = s.mem := by
  exact ⟨_, Expr.compile_exec hcode hrun,
    hrep.compiled_index b offset dst hbnd hobnd hi hb hoffset,
    (Expr.compile_correct (e := Expr.index b offset) ⟨hbnd, hobnd⟩ s).memory⟩

end ArrayRep
end Ram
