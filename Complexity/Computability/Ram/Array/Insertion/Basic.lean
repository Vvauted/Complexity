/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Verification.Loop.Basic
import Complexity.Data.List.InsertIdx
import Complexity.Tactic.Ram.Basic

/-!
# Insertion by an ordinary backward RAM traversal

Registers 0–3 hold the array base, key, insertion position, and original
length. Register 4 is the cursor. The fixed program shifts the suffix one
word at a time and writes the key; no host operation moves an array slice.
The preloaded array includes one arbitrary spare word. Its existing bounds
justify every address, including the last destination, without an extra
strict endpoint condition. The result is the standard `List.insertIdx`.
-/

namespace Ram.Source.Array.Insertion

def previous : Expr := .bin .sub (.var 4) (.const 1)
def sourceAddress : Expr := .bin .add (.var 0) previous
def destinationAddress : Expr := .bin .add (.var 0) (.var 4)
def insertionAddress : Expr := .bin .add (.var 0) (.var 2)
def condition : Expr := .bin .ult (.var 2) (.var 4)

def body : Stmt :=
  .seq (.store destinationAddress (.load sourceAddress)) (.assign 4 previous)

def loop : Stmt := .while condition body

/-- One fixed program for every representable length and insertion position. -/
def program : Stmt :=
  .seq (.assign 4 (.var 3)) (.seq loop (.store insertionAddress (.var 1)))

theorem wellFormed {locals : Nat} (h : 5 ≤ locals) : program.WellFormed locals := by
  have h0 : 0 < locals := Nat.lt_of_lt_of_le (by decide : 0 < 5) h
  have h1 : 1 < locals := Nat.lt_of_lt_of_le (by decide : 1 < 5) h
  have h2 : 2 < locals := Nat.lt_of_lt_of_le (by decide : 2 < 5) h
  have h3 : 3 < locals := Nat.lt_of_lt_of_le (by decide : 3 < 5) h
  have h4 : 4 < locals := Nat.lt_of_lt_of_le (by decide : 4 < 5) h
  simp [program, loop, body, condition, previous, sourceAddress,
    destinationAddress, insertionAddress, Stmt.WellFormed, Expr.Bounded,
    h0, h1, h2, h3, h4]

theorem body_code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable body = 14 := rfl

theorem code_size (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable program = 26 := rfl

/-- The actual state effect of one load, one store, and one decrement. -/
def stepResult (s : State w) : State w :=
  (s.setMem (s.regs 0 + s.regs 4)
    (s.mem (s.regs 0 + (s.regs 4 - 1)))).setReg 4 (s.regs 4 - 1)

@[simp] theorem stepResult_cursor (s : State w) :
    (stepResult s).regs 4 = s.regs 4 - 1 := by simp [stepResult, State.setReg]

theorem stepResult_other (s : State w) {r : Reg} (hr : r ≠ 4) :
    (stepResult s).regs r = s.regs r := by
  simp [stepResult, State.setReg, State.setMem, hr]

theorem body_contract {control heapLimit depth : Nat} {functions : Program}
    (s : State w)
    (hsource : (s.regs 0 + (s.regs 4 - 1)).toNat < heapLimit)
    (hdestination : (s.regs 0 + s.regs 4).toNat < heapLimit) :
    Contract control functions heapLimit depth body (fun t => t = s)
      (fun t => t = stepResult s) (fun _ => 14) := by
  ram_vc t ht [body, previous, sourceAddress, destinationAddress,
    stepResult, ht, hsource, hdestination]
  simpa [BitVec.toNat_add, BitVec.toNat_sub, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using hsource

/-- The initial array owns the spare last word; its value is unconstrained. -/
structure Pre (heapLimit : Nat) (base key : Word w) (position : Nat)
    (xs : List (Word w)) (spare : Word w) (s : State w) : Prop where
  array : ArrayAt heapLimit base (xs ++ [spare]) s
  base_reg : s.regs 0 = base
  key_reg : s.regs 1 = key
  position_reg : (s.regs 2).toNat = position
  length_reg : (s.regs 3).toNat = xs.length

/-- Only the allocated array and cursor may change. In particular the key,
base, position, length, and all higher registers remain available to callers. -/
structure Post (heapLimit : Nat) (base key : Word w) (position : Nat)
    (xs : List (Word w)) (entry finish : State w) : Prop where
  array : ArrayAt heapLimit base (xs.insertIdx position key) finish
  frame : ArrayFrame base (xs.length + 1) entry.mem finish.mem
  cursor : finish.regs 4 = entry.regs 2
  registers : ∀ r, r ≠ 4 → finish.regs r = entry.regs r
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev

private structure Invariant (heapLimit : Nat) (base : Word w) (position : Nat)
    (xs : List (Word w)) (spare : Word w) (entry s : State w) : Prop where
  lower : position ≤ (s.regs 4).toNat
  upper : (s.regs 4).toNat ≤ xs.length
  array : ArrayAt heapLimit base (List.Insertion.contents xs spare (s.regs 4).toNat) s
  frame : ArrayFrame base (xs.length + 1) entry.mem s.mem
  registers : ∀ r, r ≠ 4 → s.regs r = entry.regs r
  input : s.input = entry.input
  output : s.outputRev = entry.outputRev

private theorem cursor_gt {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s)
    (hz : s.eval condition ≠ 0) : position < (s.regs 4).toNat := by
  have hp : (s.regs 2).toNat = position := by
    rw [h.registers 2 (by decide), hpre.position_reg]
  have hlt := (BinOp.eval_ult_ne_zero_iff hw (s.regs 2) (s.regs 4)).mp hz
  simpa only [hp] using hlt

private theorem decrement_toNat {s : State w} (hw : 0 < w)
    (hpositive : 0 < (s.regs 4).toNat) :
    (s.regs 4 - 1).toNat = (s.regs 4).toNat - 1 := by
  have hone : (1 : Word w).toNat = 1 := BitVec.toNat_one hw
  change (BinOp.eval .sub (s.regs 4) 1).toNat = _
  rw [BinOp.eval_sub_toNat_of_le _ _ (by rw [hone]; omega), hone]

private theorem address_cursor {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w}
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s) :
    s.regs 0 + s.regs 4 = arrayAddr base (s.regs 4).toNat := by
  simp only [arrayAddr, Word.ofNat_toNat_self, h.registers 0 (by decide), hpre.base_reg]

private theorem address_previous {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s)
    (hpositive : 0 < (s.regs 4).toNat) :
    s.regs 0 + (s.regs 4 - 1) = arrayAddr base ((s.regs 4).toNat - 1) := by
  rw [arrayAddr, ← decrement_toNat hw hpositive, Word.ofNat_toNat_self,
    h.registers 0 (by decide), hpre.base_reg]

private theorem step_preserves {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s)
    (hz : s.eval condition ≠ 0) :
    Invariant heapLimit base position xs spare entry (stepResult s) ∧
      ((stepResult s).regs 4).toNat - position < (s.regs 4).toNat - position := by
  let c := (s.regs 4).toNat
  have hgt : position < c := cursor_gt hw hpre h hz
  have hpos : 0 < c := Nat.lt_of_le_of_lt (Nat.zero_le position) hgt
  have hupper : c ≤ xs.length := h.upper
  have hlen := List.Insertion.contents_length xs spare hupper
  have hc : c < (List.Insertion.contents xs spare c).length := by rw [hlen]; omega
  have hpred : c - 1 < (List.Insertion.contents xs spare c).length := by rw [hlen]; omega
  have hpredxs : c - 1 < xs.length := by omega
  have hload : s.mem (s.regs 0 + (s.regs 4 - 1)) = xs[c - 1] := by
    rw [address_previous hw hpre h hpos]
    exact (h.array.1.lookup (c - 1) hpred).trans
      (List.Insertion.contents_getElem_pred xs spare hpos hupper)
  let stored := s.setMem (arrayAddr base c) xs[c - 1]
  have hmem : (stepResult s).mem = stored.mem := by
    change (s.setMem (s.regs 0 + s.regs 4)
      (s.mem (s.regs 0 + (s.regs 4 - 1)))).mem = stored.mem
    rw [address_cursor hpre h, hload]
  have hframe : ArrayFrame base (xs.length + 1) s.mem (stepResult s).mem := by
    rw [hmem]
    have hf : ArrayFrame base (List.Insertion.contents xs spare c).length s.mem stored.mem :=
      ArrayFrame.store h.array.1 hc xs[c - 1]
    rw [hlen] at hf
    exact hf
  have harray : ArrayAt heapLimit base (List.Insertion.contents xs spare (c - 1)) (stepResult s) := by
    have ha := h.array.setMem hc xs[c - 1]
    rw [List.Insertion.contents_shift xs spare hpos hupper] at ha
    change ArrayRep (stepResult s).mem base _ ∧ _
    rw [hmem]
    exact ha
  have hdec : ((stepResult s).regs 4).toNat = c - 1 := by
    rw [stepResult_cursor, decrement_toNat hw hpos]
  refine ⟨⟨?_, ?_, ?_, h.frame.trans hframe, ?_, h.input, h.output⟩, ?_⟩
  · rw [hdec]; omega
  · rw [hdec]; omega
  · rw [hdec]; exact harray
  · intro r hr
    exact (stepResult_other s hr).trans (h.registers r hr)
  · rw [hdec]; omega

private theorem exit_cursor {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s)
    (hz : s.eval condition = 0) : (s.regs 4).toNat = position := by
  have hp : (s.regs 2).toNat = position := by
    rw [h.registers 2 (by decide), hpre.position_reg]
  have hn : ¬ position < (s.regs 4).toNat := by
    intro hlt
    have he : s.eval condition ≠ 0 :=
      (BinOp.eval_ult_ne_zero_iff hw (s.regs 2) (s.regs 4)).mpr (by simpa [hp] using hlt)
    exact he hz
  exact Nat.le_antisymm (Nat.le_of_not_gt hn) h.lower

private theorem finish_post {heapLimit position : Nat} {base key spare : Word w}
    {xs : List (Word w)} {entry s : State w} (hw : 0 < w)
    (hpre : Pre heapLimit base key position xs spare entry)
    (h : Invariant heapLimit base position xs spare entry s)
    (hz : s.eval condition = 0) :
    Post heapLimit base key position xs entry
      (s.setMem (s.regs 0 + s.regs 2) (s.regs 1)) := by
  have hc := exit_cursor hw hpre h hz
  have hp : position ≤ xs.length := by simpa only [hc] using h.upper
  have ha : ArrayAt heapLimit base (List.Insertion.contents xs spare position) s := by
    simpa only [hc] using h.array
  have hlen := List.Insertion.contents_length xs spare hp
  have hindex : position < (List.Insertion.contents xs spare position).length := by rw [hlen]; omega
  have haddress : s.regs 0 + s.regs 2 = arrayAddr base position := by
    rw [h.registers 0 (by decide), hpre.base_reg, h.registers 2 (by decide),
      arrayAddr, ← hpre.position_reg, Word.ofNat_toNat_self]
  have hkey : s.regs 1 = key := (h.registers 1 (by decide)).trans hpre.key_reg
  rw [haddress, hkey]
  refine ⟨?_, ?_, ?_, h.registers, h.input, h.output⟩
  · have hs := ha.setMem hindex key
    rw [List.Insertion.contents_set_eq_insertIdx xs spare key hp] at hs
    exact hs
  · have hf : ArrayFrame base (List.Insertion.contents xs spare position).length s.mem
        (s.setMem (arrayAddr base position) key).mem := ArrayFrame.store ha.1 hindex key
    rw [hlen] at hf
    exact h.frame.trans hf
  · change s.regs 4 = entry.regs 2
    exact BitVec.eq_of_toNat_eq (hc.trans hpre.position_reg.symm)

/-- A reusable preloaded-array insertion contract. The generated body has
fourteen instructions; its guard costs four and its back-edge one, so each
shift costs nineteen. Initialization, the final guard, and the final store
cost eleven. Every step is an ordinary instruction of the existing compiler. -/
theorem contract {control heapLimit depth : Nat} {functions : Program}
    {base key spare : Word w} {position : Nat} {xs : List (Word w)}
    (hw : 0 < w) (hp : position ≤ xs.length) :
    RelContract control functions heapLimit depth program
      (Pre heapLimit base key position xs spare)
      (Post heapLimit base key position xs)
      (fun _ => 19 * (xs.length - position) + 11) := by
  intro entry hpre
  let initialized := entry.setReg 4 (entry.regs 3)
  have hinit : Contract control functions heapLimit depth (.assign 4 (.var 3))
      (fun s => s = entry) (fun s => s = initialized) (fun _ => 2) := by
    ram_vc s hs [initialized, hs]
  have hstart : Invariant heapLimit base position xs spare entry initialized := by
    have hc : (initialized.regs 4).toNat = xs.length := by
      simp [initialized, State.setReg, hpre.length_reg]
    refine ⟨?_, ?_, ?_, ArrayFrame.refl _ _ _, ?_, rfl, rfl⟩
    · rw [hc]; exact hp
    · rw [hc]
    · rw [hc, List.Insertion.contents_initial]
      exact hpre.array.setReg 4 (entry.regs 3)
    · intro r hr
      simp [initialized, State.setReg, hr]
  have hloop : Contract control functions heapLimit depth loop
      (Invariant heapLimit base position xs spare entry)
      (fun s => Invariant heapLimit base position xs spare entry s ∧ s.eval condition = 0)
      (fun s => ((s.regs 4).toNat - position) * 19 + 4) := by
    apply Contract.while_linear (Invariant heapLimit base position xs spare entry)
      (fun s => (s.regs 4).toNat - position) 14
    · intro s hs
      trivial
    · intro s hs hz
      have hgt := cursor_gt hw hpre hs hz
      have hpos : 0 < (s.regs 4).toNat := Nat.lt_of_le_of_lt (Nat.zero_le position) hgt
      have hlen := List.Insertion.contents_length xs spare hs.upper
      have hsource : (s.regs 0 + (s.regs 4 - 1)).toNat < heapLimit := by
        rw [address_previous hw hpre hs hpos]
        apply hs.array.addr_lt
        rw [hlen]
        have hu := hs.upper
        omega
      have hdestination : (s.regs 0 + s.regs 4).toNat < heapLimit := by
        rw [address_cursor hpre hs]
        apply hs.array.addr_lt
        rw [hlen]
        exact Nat.lt_succ_of_le hs.upper
      apply (body_contract s hsource hdestination).mono_post
      intro t ht
      subst t
      exact step_preserves hw hpre hs hz
  obtain ⟨ni, si, hxi, hsi, hbi⟩ := hinit entry rfl
  subst si
  obtain ⟨nl, sl, hxl, hsl, hbl⟩ := hloop initialized hstart
  have hc := exit_cursor hw hpre hsl.1 hsl.2
  have haddress : sl.regs 0 + sl.regs 2 = arrayAddr base position := by
    rw [hsl.1.registers 0 (by decide), hpre.base_reg, hsl.1.registers 2 (by decide),
      arrayAddr, ← hpre.position_reg, Word.ofNat_toNat_self]
  have hsafe : (sl.regs 0 + sl.regs 2).toNat < heapLimit := by
    rw [haddress]
    apply hsl.1.array.addr_lt
    rw [List.Insertion.contents_length xs spare hsl.1.upper]
    exact Nat.lt_succ_of_le hp
  have hfinal : Contract control functions heapLimit depth (.store insertionAddress (.var 1))
      (fun s => s = sl)
      (fun s => s = sl.setMem (sl.regs 0 + sl.regs 2) (sl.regs 1)) (fun _ => 5) := by
    ram_vc s hs [insertionAddress, hs, hsafe]
  obtain ⟨nf, sf, hxf, hsf, hbf⟩ := hfinal sl rfl
  subst sf
  refine ⟨ni + (nl + nf), _, .seq hxi (.seq hxl hxf),
    finish_post hw hpre hsl.1 hsl.2, ?_⟩
  change ni ≤ 2 at hbi
  change nf ≤ 5 at hbf
  change nl ≤ ((initialized.regs 4).toNat - position) * 19 + 4 at hbl
  have hcinit : (initialized.regs 4).toNat = xs.length := by
    simp [initialized, State.setReg, hpre.length_reg]
  rw [hcinit, Nat.mul_comm] at hbl
  change ni + (nl + nf) ≤ 19 * (xs.length - position) + 11
  omega

end Ram.Source.Array.Insertion
