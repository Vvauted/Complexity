/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic

/-!
# Sequential field-copy execution

`copyFields` evaluates its operands one at a time. Its result equals a snapshot
of the original operand values when the copied expressions do not read the
destination range. A single assignment needs no separation premise. Heap loads
are permitted: both their values and their heap-safety facts are preserved by
the preceding register writes. Counts are the actual emitted statement size.
-/

namespace Ram.Expr

/-- Every register read by the expression is outside the half-open interval
`[dst, dst + count)`. Loads inherit the condition of their address expression. -/
def AvoidsRange : Expr → Nat → Nat → Prop
  | .const _, _, _ => True
  | .var register, dst, count => register < dst ∨ dst + count ≤ register
  | .bin _ lhs rhs, dst, count => lhs.AvoidsRange dst count ∧ rhs.AvoidsRange dst count
  | .load address, dst, count => address.AvoidsRange dst count

/-- Avoiding an interval also avoids each of its subintervals. -/
theorem AvoidsRange.mono {expr : Expr} {dst count dst' count' : Nat}
    (avoids : expr.AvoidsRange dst count) (start : dst ≤ dst')
    (finish : dst' + count' ≤ dst + count) : expr.AvoidsRange dst' count' := by
  induction expr with
  | const => trivial
  | var register =>
      change register < dst ∨ dst + count ≤ register at avoids
      change register < dst' ∨ dst' + count' ≤ register
      rcases avoids with before | after
      · exact Or.inl (Nat.lt_of_lt_of_le before start)
      · exact Or.inr (Nat.le_trans finish after)
  | bin op lhs rhs left right => exact ⟨left avoids.1, right avoids.2⟩
  | load address ih => exact ih avoids

/-- Writing inside an avoided interval preserves actual expression evaluation,
including addresses and values of nested memory reads. -/
theorem AvoidsRange.eval_setReg {expr : Expr} {dst count register : Nat}
    (avoids : expr.AvoidsRange dst count) (entry : Source.State w) (value : Word w)
    (start : dst ≤ register) (finish : register < dst + count) :
    (entry.setReg register value).eval expr = entry.eval expr := by
  induction expr with
  | const => rfl
  | var source =>
      change (entry.setReg register value).regs source = entry.regs source
      apply Source.State.setReg_ne
      change source < dst ∨ dst + count ≤ source at avoids
      rcases avoids with before | after
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le before start)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le finish after)
  | bin op lhs rhs left right =>
      change op.eval ((entry.setReg register value).eval lhs)
        ((entry.setReg register value).eval rhs) =
        op.eval (entry.eval lhs) (entry.eval rhs)
      rw [left avoids.1, right avoids.2]
  | load address ih =>
      change entry.mem ((entry.setReg register value).eval address) =
        entry.mem (entry.eval address)
      rw [ih avoids]

/-- The same noninterference preserves all actual heap-read bounds, not just
the expression's final value. -/
theorem AvoidsRange.readsBelow_setReg {expr : Expr} {dst count register limit : Nat}
    (avoids : expr.AvoidsRange dst count) (entry : Source.State w) (value : Word w)
    (start : dst ≤ register) (finish : register < dst + count)
    (reads : expr.ReadsBelow limit entry.regs entry.mem) :
    expr.ReadsBelow limit (entry.setReg register value).regs
      (entry.setReg register value).mem := by
  induction expr with
  | const => trivial
  | var => trivial
  | bin op lhs rhs left right => exact ⟨left avoids.1 reads.1, right avoids.2 reads.2⟩
  | load address ih =>
      refine ⟨ih avoids reads.1, ?_⟩
      change ((entry.setReg register value).eval address).toNat < limit
      have addressAvoids : address.AvoidsRange dst count := avoids
      rw [addressAvoids.eval_setReg entry value start finish]
      exact reads.2

end Ram.Expr

namespace Ram.LanguageCompiler

/-- Sequential copying produces the original operand values in order. Singleton
copies allow arbitrary aliasing; longer copies keep every operand disjoint from
the destination interval. The exact count comes from the emitted code. -/
theorem copyFields_localMeasured {control heapLimit depth : Nat} {program : Program}
    (entry : Source.State w) (dst : Reg) (exprs : List Expr)
    (reads : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (separated : exprs.length ≤ 1 ∨ ∀ expr ∈ exprs, expr.AvoidsRange dst exprs.length) :
    Source.LocalMeasuredExec control program heapLimit depth (copyFields dst exprs)
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) (copyFields dst exprs))
      entry (entry.setRegs (List.range' dst exprs.length) (exprs.map entry.eval)) := by
  induction exprs generalizing entry dst with
  | nil => simpa only [copyFields, List.length_nil, List.range'_zero,
      Source.State.setRegs_nil, LocalCompiler.stmtSize_skip] using
        (Source.LocalMeasuredExec.skip (control := control) (program := program)
          (heapLimit := heapLimit) (d := depth) (s := entry))
  | cons expr rest ih =>
      cases rest with
      | nil =>
          simpa only [copyFields, List.length_cons, List.length_nil,
            List.range'_succ, List.range'_zero, List.map_cons, List.map_nil,
            Source.State.setRegs_singleton] using
              (Source.LocalMeasuredExec.assign (control := control) (program := program)
                (d := depth) (dst := dst) (reads expr (by simp)))
      | cons next rest =>
          have avoids : ∀ operand ∈ expr :: next :: rest,
              operand.AvoidsRange dst (expr :: next :: rest).length :=
            separated.resolve_left (by
              intro short
              simp only [List.length_cons] at short
              omega)
          have inRange : dst < dst + (expr :: next :: rest).length := by
            change dst < dst + (rest.length + 1 + 1)
            exact Nat.lt_add_of_pos_right (Nat.succ_pos (rest.length + 1))
          have tailReads : ∀ operand ∈ next :: rest,
              operand.ReadsBelow heapLimit (entry.setReg dst (entry.eval expr)).regs
                (entry.setReg dst (entry.eval expr)).mem := by
            intro operand member
            exact (avoids operand (List.mem_cons_of_mem _ member)).readsBelow_setReg
              entry (entry.eval expr) (Nat.le_refl dst) inRange
              (reads operand (List.mem_cons_of_mem _ member))
          have tailAvoids : ∀ operand ∈ next :: rest,
              operand.AvoidsRange (dst + 1) (next :: rest).length := by
            intro operand member
            exact (avoids operand (List.mem_cons_of_mem _ member)).mono (by omega)
              (by simp only [List.length_cons]; omega)
          have values : (next :: rest).map (entry.setReg dst (entry.eval expr)).eval =
              (next :: rest).map entry.eval := by
            apply List.map_congr_left
            intro operand member
            exact (avoids operand (List.mem_cons_of_mem _ member)).eval_setReg
              entry (entry.eval expr) (Nat.le_refl dst) inRange
          have tailExec := ih (entry.setReg dst (entry.eval expr)) (dst + 1)
            tailReads (Or.inr tailAvoids)
          rw [values] at tailExec
          have execution := Source.LocalMeasuredExec.seq
            (Source.LocalMeasuredExec.assign (dst := dst) (reads expr (by simp))) tailExec
          simpa only [copyFields, LocalCompiler.stmtSize_seq, List.length_cons,
            List.range'_succ, List.map_cons, Source.State.setRegs_cons] using execution

/-- Erasing the derived instruction count gives the same safe copy execution. -/
theorem copyFields_safe {heapLimit depth : Nat} {program : Program}
    (entry : Source.State w) (dst : Reg) (exprs : List Expr)
    (reads : ∀ expr ∈ exprs, expr.ReadsBelow heapLimit entry.regs entry.mem)
    (separated : exprs.length ≤ 1 ∨ ∀ expr ∈ exprs, expr.AvoidsRange dst exprs.length) :
    Source.SafeExec program heapLimit depth (copyFields dst exprs)
      entry (entry.setRegs (List.range' dst exprs.length) (exprs.map entry.eval)) :=
  (copyFields_localMeasured (control := 0) entry dst exprs reads separated).erase

end Ram.LanguageCompiler
