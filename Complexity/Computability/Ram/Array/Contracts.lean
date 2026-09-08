/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Basic
import Complexity.Computability.Ram.Verification.Contract
import Init.Data.List.Nat.Perm

/-!
# Reusable heap-array contracts

Logical contents use the existing `ArrayRep` and standard `List.getElem` /
`List.set` API. The contracts retain their entry state as a ghost and record
unchanged memory outside the array, so disjoint arrays need no fresh proof.
Programs use ordinary source loads, stores and assignments; their budgets
are the lengths of the concrete generated instruction blocks.
-/

namespace Ram

/-- Memory outside this half-open array interval is unchanged. -/
def ArrayFrame (base : Word w) (len : Nat)
    (before after : Word w → Word w) : Prop :=
  ∀ address, address.toNat < base.toNat ∨ base.toNat + len ≤ address.toNat →
    after address = before address

/-- The two mathematical address intervals do not overlap. -/
def ArraysDisjoint (base : Word w) (len : Nat) (other : Word w) (otherLen : Nat) : Prop :=
  base.toNat + len ≤ other.toNat ∨ other.toNat + otherLen ≤ base.toNat

namespace ArrayFrame

theorem refl (base : Word w) (len : Nat) (mem : Word w → Word w) :
    ArrayFrame base len mem mem := fun _ _ => rfl

theorem trans {base : Word w} {len : Nat} {before middle after : Word w → Word w}
    (first : ArrayFrame base len before middle)
    (second : ArrayFrame base len middle after) : ArrayFrame base len before after :=
  fun address hout => (second address hout).trans (first address hout)

/-- A valid array-element store leaves every address outside the array alone. -/
theorem store {mem : Word w → Word w} {base : Word w} {xs : List (Word w)}
    (hrep : ArrayRep mem base xs) {i : Nat} (hi : i < xs.length) (value : Word w) :
    ArrayFrame base xs.length mem
      (fun address => if address = arrayAddr base i then value else mem address) := by
  intro address hout
  have hne : address ≠ arrayAddr base i := by
    intro he
    subst address
    rw [hrep.addr_toNat hi] at hout
    omega
  exact if_neg hne

/-- A framed update preserves a separately represented, disjoint array. -/
theorem preserves {base other : Word w} {len : Nat}
    {before after : Word w → Word w} {ys : List (Word w)}
    (hframe : ArrayFrame base len before after)
    (hdisjoint : ArraysDisjoint base len other ys.length)
    (hother : ArrayRep before other ys) : ArrayRep after other ys := by
  refine ⟨hother.fits, ?_⟩
  intro i hi
  have hout : (arrayAddr other i).toNat < base.toNat ∨
      base.toNat + len ≤ (arrayAddr other i).toNat := by
    rw [hother.addr_toNat hi]
    unfold ArraysDisjoint at hdisjoint
    omega
  exact (hframe (arrayAddr other i) hout).trans (hother.lookup i hi)

end ArrayFrame

namespace Source

/-- A logical array representation whose full interval lies inside the heap. -/
def ArrayAt (heapLimit : Nat) (base : Word w) (xs : List (Word w)) (s : State w) : Prop :=
  ArrayRep s.mem base xs ∧ base.toNat + xs.length ≤ heapLimit

namespace ArrayAt

theorem addr_lt {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {i : Nat} (hi : i < xs.length) :
    (arrayAddr base i).toNat < heapLimit := by
  rw [h.1.addr_toNat hi]
  have hheap := h.2
  omega

theorem setReg {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) (dst : Reg) (value : Word w) :
    ArrayAt heapLimit base xs (s.setReg dst value) := h

theorem setMem {heapLimit : Nat} {base : Word w} {xs : List (Word w)}
    {s : State w} (h : ArrayAt heapLimit base xs s) {i : Nat} (hi : i < xs.length)
    (value : Word w) :
    ArrayAt heapLimit base (xs.set i value) (s.setMem (arrayAddr base i) value) := by
  exact ⟨h.1.store hi value, by simpa using h.2⟩

/-- A disjoint array assertion survives any update with the indicated frame. -/
theorem frame {heapLimit len : Nat} {base other : Word w} {ys : List (Word w)}
    {s t : State w} (h : ArrayAt heapLimit other ys s)
    (hframe : ArrayFrame base len s.mem t.mem)
    (hdisjoint : ArraysDisjoint base len other ys.length) :
    ArrayAt heapLimit other ys t :=
  ⟨hframe.preserves hdisjoint h.1, h.2⟩

end ArrayAt
end Source
end Ram

namespace Ram.Source.Array

/-- Load one represented element. The exact state update also records that
the entire heap and all other source registers are unchanged. -/
theorem read_contract {control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} {i : Nat} (hi : i < xs.length)
    (dst : Reg) (address : Expr) :
    RelContract control program heapLimit depth (.assign dst (.load address))
      (fun s => ArrayAt heapLimit base xs s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧ s.eval address = arrayAddr base i)
      (fun entry finish => finish = entry.setReg dst xs[i] ∧
        ArrayAt heapLimit base xs finish)
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.assign dst (.load address))) := by
  apply RelContract.iff_entry.mpr
  intro entry ⟨harray, hreads, haddress⟩
  apply Contract.assign
  · intro s hs
    subst s
    refine ⟨hreads, ?_⟩
    change (entry.eval address).toNat < heapLimit
    rw [haddress]
    exact harray.addr_lt hi
  · intro s hs
    subst s
    have hvalue : entry.eval (.load address) = xs[i] := by
      change entry.mem (entry.eval address) = xs[i]
      rw [haddress]
      exact harray.1.lookup i hi
    rw [hvalue]
    exact ⟨rfl, harray.setReg dst xs[i]⟩

/-- Store one element with the standard `List.set` semantics. The returned
frame is sufficient to preserve any separately represented disjoint array. -/
theorem store_contract {control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} {i : Nat} (hi : i < xs.length)
    (address value : Expr) (stored : Word w) :
    RelContract control program heapLimit depth (.store address value)
      (fun s => ArrayAt heapLimit base xs s ∧
        address.ReadsBelow heapLimit s.regs s.mem ∧
        value.ReadsBelow heapLimit s.regs s.mem ∧
        s.eval address = arrayAddr base i ∧ s.eval value = stored)
      (fun entry finish => finish = entry.setMem (arrayAddr base i) stored ∧
        ArrayAt heapLimit base (xs.set i stored) finish ∧
        ArrayFrame base xs.length entry.mem finish.mem)
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.store address value)) := by
  apply RelContract.iff_entry.mpr
  intro entry ⟨harray, haddressReads, hvalueReads, haddress, hvalue⟩
  apply Contract.store
  · intro s hs
    subst s
    exact haddressReads
  · intro s hs
    subst s
    exact hvalueReads
  · intro s hs
    subst s
    rw [haddress]
    exact harray.addr_lt hi
  · intro s hs
    subst s
    rw [haddress, hvalue]
    exact ⟨rfl, harray.setMem hi stored, ArrayFrame.store harray.1 hi stored⟩

/-- An address obtained from runtime base and index registers. -/
def address (base index : Reg) : Expr := .bin .add (.var base) (.var index)

/-- Swap two array elements using one temporary register and three ordinary
statements. The old element is saved before either heap write. -/
def swap (base first second temporary : Reg) : Stmt :=
  .seq (.assign temporary (.load (address base first)))
    (.seq (.store (address base first) (.load (address base second)))
      (.store (address base second) (.var temporary)))

/-- The fixed swap code emits eighteen actual instructions. -/
theorem swap_code_size (control : Nat) (localsTable : Nat → Nat)
    (base first second temporary : Reg) :
    LocalCompiler.stmtSize control localsTable (swap base first second temporary) = 18 := rfl

theorem swap_wellFormed {locals base first second temporary : Nat}
    (hb : base < locals) (hi : first < locals) (hj : second < locals)
    (ht : temporary < locals) : (swap base first second temporary).WellFormed locals := by
  simp [swap, address, Stmt.WellFormed, Expr.Bounded, hb, hi, hj, ht]

/-- The standard list permutation theorem also covers equal indices. -/
theorem swap_contents_perm {xs : List (Word w)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := List.set_set_perm hi hj

/-- A runtime-indexed swap preserves every array-external word. The temporary
must not alias the registers used to compute either address. No `i ≠ j`
premise is needed: equal indices are a valid no-op on the logical contents. -/
theorem swap_contract {control heapLimit depth : Nat} {program : Program}
    {base : Word w} {xs : List (Word w)} {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length)
    (baseReg first second temporary : Reg)
    (hbase : baseReg ≠ temporary) (hfirst : first ≠ temporary)
    (hsecond : second ≠ temporary) :
    RelContract control program heapLimit depth (swap baseReg first second temporary)
      (fun s => ArrayAt heapLimit base xs s ∧ s.regs baseReg = base ∧
        s.regs first = BitVec.ofNat w i ∧ s.regs second = BitVec.ofNat w j)
      (fun entry finish =>
        finish = ((entry.setReg temporary xs[i]).setMem (arrayAddr base i) xs[j]).setMem
          (arrayAddr base j) xs[i] ∧
        ArrayAt heapLimit base ((xs.set i xs[j]).set j xs[i]) finish ∧
        ArrayFrame base xs.length entry.mem finish.mem)
      (fun _ => LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (swap baseReg first second temporary)) := by
  apply RelContract.iff_entry.mpr
  intro entry ⟨harray, hb, hri, hrj⟩
  let saved := entry.setReg temporary xs[i]
  let middle := saved.setMem (arrayAddr base i) xs[j]
  have hsaved : ArrayAt heapLimit base xs saved := harray.setReg temporary xs[i]
  have hmiddle : ArrayAt heapLimit base (xs.set i xs[j]) middle := hsaved.setMem hi xs[j]
  have haj : j < (xs.set i xs[j]).length := by simpa using hj
  have hai : entry.eval (address baseReg first) = arrayAddr base i := by
    simp [address, State.eval, Expr.eval, BinOp.eval, arrayAddr, hb, hri]
  have hsai : saved.eval (address baseReg first) = arrayAddr base i := by
    simp [saved, address, State.eval, Expr.eval, BinOp.eval, arrayAddr,
      State.setReg, hbase, hfirst, hb, hri]
  have hsaj : saved.eval (address baseReg second) = arrayAddr base j := by
    simp [saved, address, State.eval, Expr.eval, BinOp.eval, arrayAddr,
      State.setReg, hbase, hsecond, hb, hrj]
  have hmaj : middle.eval (address baseReg second) = arrayAddr base j := hsaj
  have hvj : saved.eval (.load (address baseReg second)) = xs[j] := by
    change saved.mem (saved.eval (address baseReg second)) = xs[j]
    rw [hsaj]
    exact hsaved.1.lookup j hj
  have hvtmp : middle.eval (.var temporary) = xs[i] := by
    simp [middle, saved]
  have hframe : ArrayFrame base xs.length entry.mem middle.mem :=
    ArrayFrame.store harray.1 hi xs[j]
  have hload : Contract control program heapLimit depth
      (.assign temporary (.load (address baseReg first)))
      (fun s => s = entry) (fun s => s = saved) (fun _ => 5) := by
    have h := RelContract.iff_entry.mp
      (read_contract (control := control) (program := program) (depth := depth)
        hi temporary (address baseReg first)) entry ⟨harray, ⟨trivial, trivial⟩, hai⟩
    exact h.mono_post (fun _ ht => ht.1)
  have hstoreFirst : Contract control program heapLimit depth
      (.store (address baseReg first) (.load (address baseReg second)))
      (fun s => s = saved) (fun s => s = middle) (fun _ => 8) := by
    have hreads : (Expr.load (address baseReg second)).ReadsBelow heapLimit saved.regs saved.mem :=
      ⟨⟨trivial, trivial⟩, by
        change (saved.eval (address baseReg second)).toNat < heapLimit
        rw [hsaj]
        exact hsaved.addr_lt hj⟩
    have h := RelContract.iff_entry.mp
      (store_contract (control := control) (program := program) (depth := depth)
        hi (address baseReg first) (.load (address baseReg second)) xs[j])
      saved ⟨hsaved, ⟨trivial, trivial⟩, hreads, hsai, hvj⟩
    exact h.mono_post (fun _ ht => ht.1)
  have hstoreSecond : Contract control program heapLimit depth
      (.store (address baseReg second) (.var temporary)) (fun s => s = middle)
      (fun finish => finish = middle.setMem (arrayAddr base j) xs[i] ∧
        ArrayAt heapLimit base ((xs.set i xs[j]).set j xs[i]) finish ∧
        ArrayFrame base xs.length entry.mem finish.mem) (fun _ => 5) := by
    have h := RelContract.iff_entry.mp
      (store_contract (control := control) (program := program) (depth := depth)
        haj (address baseReg second) (.var temporary) xs[i])
      middle ⟨hmiddle, ⟨trivial, trivial⟩, trivial, hmaj, hvtmp⟩
    apply h.mono_post
    intro finish ⟨heq, harr, hf⟩
    refine ⟨heq, harr, hframe.trans ?_⟩
    simpa only [List.length_set] using hf
  exact hload.seq_const (hstoreFirst.seq_const hstoreSecond)

end Ram.Source.Array
