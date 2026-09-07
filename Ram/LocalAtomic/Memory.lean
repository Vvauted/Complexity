/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.LocalAtomic
import Ram.ExprCompile.Memory

/-!
# Actual heap footprints of compiled atomic statements

The source-to-target matching relation transports source expression read bounds
to the real instructions emitted for assignment, store, and output. Expression
temporaries and private stack memory need not agree with the source state.

Assignments and I/O instructions make no heap writes. A compiled store writes
exactly its source address, even when the stored value equals the previous value.
Its two expression evaluations can also read the heap; these accesses are
included in the bound, not discarded as internal compiler work.

These are observations of the existing machine execution. Bounds are proof
premises, not additional runtime checks. Input reads have empty heap footprints
even when the input is empty and the read instruction faults.
-/

namespace Ram.LocalAtomic

private theorem locals_le_scratch {locals control : Nat} (h : locals ≤ control) :
    locals ≤ ABI.scratch control := by
  simp only [ABI.scratch]
  omega

private theorem expr_access_below {locals heapLimit scratch : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (matched : Source.State.Matches heapLimit locals s t)
    (fresh : locals ≤ scratch) (bounded : e.Bounded locals)
    (reads : e.ReadsBelow heapLimit s.regs s.mem)
    (atExpr : CodeAt code t.pc (e.compile scratch)) {address : Word w}
    (member : address ∈ heapAccesses code (e.compile scratch).length t) :
    address.toNat < heapLimit :=
  Expr.compile_heapAccesses_below (bounded.mono fresh)
    (Expr.readsBelow_congr bounded reads matched.regs matched.heap)
    atExpr matched.running member

private theorem expr_tail_memory {code : Code} {e : Expr} {scratch : Reg}
    {last : Instr} {t : State w}
    (atBlock : CodeAt code t.pc (e.compile scratch ++ [last]))
    (running : t.status = .running) :
    heapAccesses code (e.compile scratch ++ [last]).length t =
        heapAccesses code (e.compile scratch).length t ∪
          last.heapAccesses (execBlock (e.compile scratch) t) ∧
      heapWrites code (e.compile scratch ++ [last]).length t =
        last.heapWrites (execBlock (e.compile scratch) t) := by
  have expressionRun := Expr.compile_exec atBlock.append_left running
  have evaluatedRunning :=
    (execBlock_status _ t (Expr.compile_linear e scratch)).trans running
  have atLast : CodeAt code (execBlock (e.compile scratch) t).pc [last] := by
    rw [execBlock_pc _ t (Expr.compile_linear e scratch)]
    exact atBlock.append_right
  constructor
  · rw [List.length_append, List.length_singleton, heapAccesses_add expressionRun 1,
      heapAccesses_one, stepHeapAccesses_of_fetch evaluatedRunning atLast.head]
  · rw [List.length_append, List.length_singleton, heapWrites_add expressionRun 1,
      Expr.compile_heapWrites_eq_empty atBlock.append_left running,
      heapWrites_one, stepHeapWrites_of_fetch evaluatedRunning atLast.head,
      Finset.empty_union]

/-- Assignment's only heap accesses are those of its value expression, and
source matching places each of them below the source-heap boundary. -/
theorem assign_heapAccesses_below {control locals heapLimit dst : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (bounded : e.Bounded locals) (reads : e.ReadsBelow heapLimit s.regs s.mem)
    (atAssign : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]))
    {address : Word w}
    (member : address ∈ heapAccesses code
      (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]).length t) :
    address.toNat < heapLimit := by
  rw [(expr_tail_memory atAssign matched.running).1] at member
  simp only [Instr.heapAccesses, Finset.union_empty] at member
  exact expr_access_below matched (locals_le_scratch hlocals) bounded reads
    atAssign.append_left member

/-- A compiled assignment performs no actual heap write, regardless of its
value expression or destination register. -/
theorem assign_heapWrites_eq_empty {control dst : Nat} {code : Code}
    {t : State w} {e : Expr}
    (atAssign : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]))
    (running : t.status = .running) :
    heapWrites code
      (e.compile (ABI.scratch control) ++ [Instr.move dst (ABI.scratch control)]).length t = ∅ :=
  (expr_tail_memory atAssign running).2

/-- Output evaluates its expression before writing the I/O stream. Only that
expression can access heap words, all within the source read bound. -/
theorem write_heapAccesses_below {control locals heapLimit : Nat} {code : Code}
    {s : Source.State w} {t : State w} {e : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (bounded : e.Bounded locals) (reads : e.ReadsBelow heapLimit s.regs s.mem)
    (atWrite : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]))
    {address : Word w}
    (member : address ∈ heapAccesses code
      (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]).length t) :
    address.toNat < heapLimit := by
  rw [(expr_tail_memory atWrite matched.running).1] at member
  simp only [Instr.heapAccesses, Finset.union_empty] at member
  exact expr_access_below matched (locals_le_scratch hlocals) bounded reads
    atWrite.append_left member

/-- Writing to the output stream is not a heap store. -/
theorem write_heapWrites_eq_empty {control : Nat} {code : Code} {t : State w} {e : Expr}
    (atWrite : CodeAt code t.pc
      (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]))
    (running : t.status = .running) :
    heapWrites code
      (e.compile (ABI.scratch control) ++ [Instr.write (ABI.scratch control)]).length t = ∅ :=
  (expr_tail_memory atWrite running).2

/-- Reading input has no heap accesses, including when the instruction faults
because input is empty. The instruction is still fetched and executed. -/
theorem read_heapAccesses_eq_empty {dst : Nat} {code : Code} {t : State w}
    (atRead : CodeAt code t.pc [Instr.read dst]) (running : t.status = .running) :
    heapAccesses code 1 t = ∅ := by
  rw [heapAccesses_one, stepHeapAccesses_of_fetch running atRead.head]
  rfl

/-- Input reads cannot write the heap. -/
theorem read_heapWrites_eq_empty {dst : Nat} {code : Code} {t : State w}
    (atRead : CodeAt code t.pc [Instr.read dst]) (running : t.status = .running) :
    heapWrites code 1 t = ∅ := by
  rw [heapWrites_one, stepHeapWrites_of_fetch running atRead.head]
  rfl

private theorem store_memory {code : Code} {scratch : Reg} {t : State w}
    {address value : Expr}
    (atStore : CodeAt code t.pc (address.compile scratch ++ value.compile (scratch + 1) ++
      [Instr.store scratch (scratch + 1)])) (running : t.status = .running) :
    let ta := execBlock (address.compile scratch) t
    let tv := execBlock (value.compile (scratch + 1)) ta
    heapAccesses code (address.compile scratch ++ value.compile (scratch + 1) ++
        [Instr.store scratch (scratch + 1)]).length t =
      heapAccesses code (address.compile scratch).length t ∪
        heapAccesses code (value.compile (scratch + 1)).length ta ∪ {tv.regs scratch} ∧
    heapWrites code (address.compile scratch ++ value.compile (scratch + 1) ++
        [Instr.store scratch (scratch + 1)]).length t = {tv.regs scratch} := by
  let ta := execBlock (address.compile scratch) t
  have atAddress : CodeAt code t.pc (address.compile scratch) := atStore.append_left.append_left
  have addressRun : Exec code (address.compile scratch).length t ta :=
    Expr.compile_exec atAddress running
  have addressRunning : ta.status = .running :=
    (execBlock_status _ t (Expr.compile_linear address scratch)).trans running
  have atTail : CodeAt code ta.pc
      (value.compile (scratch + 1) ++ [Instr.store scratch (scratch + 1)]) := by
    rw [execBlock_pc _ t (Expr.compile_linear address scratch)]
    apply CodeAt.append_right
    simpa only [List.append_assoc] using atStore
  have tailMemory := expr_tail_memory atTail addressRunning
  constructor
  · simp only [List.length_append, List.length_singleton] at tailMemory ⊢
    rw [Nat.add_assoc, heapAccesses_add addressRun _, tailMemory.1]
    exact (Finset.union_assoc _ _ _).symm
  · simp only [List.length_append, List.length_singleton] at tailMemory ⊢
    rw [Nat.add_assoc, heapWrites_add addressRun _,
      Expr.compile_heapWrites_eq_empty atAddress running, Finset.empty_union, tailMemory.2]
    rfl

private theorem store_address_eq {control locals heapLimit : Nat}
    {s : Source.State w} {t : State w} {address value : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (ha : address.Bounded locals) (hv : value.Bounded locals)
    (har : address.ReadsBelow heapLimit s.regs s.mem) :
    (execBlock (value.compile (ABI.scratch control + 1))
      (execBlock (address.compile (ABI.scratch control)) t)).regs (ABI.scratch control) =
        s.eval address := by
  have fresh := locals_le_scratch hlocals
  have evaluated := matched.compile_expr ha har fresh
  exact ((Expr.compile_correct (hv.mono (fresh.trans (Nat.le_succ _)))
    (execBlock (address.compile (ABI.scratch control)) t)).below _
    (Nat.lt_succ_self _)).trans evaluated.2

/-- The only actual write is the source store address. The address read bound
ensures source/target evaluation agrees; the value's read bound and destination
bound are not needed merely to identify this write set. -/
theorem store_heapWrites_eq_singleton {control locals heapLimit : Nat} {code : Code}
    {s : Source.State w} {t : State w} {address value : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (ha : address.Bounded locals) (hv : value.Bounded locals)
    (har : address.ReadsBelow heapLimit s.regs s.mem)
    (atStore : CodeAt code t.pc (address.compile (ABI.scratch control) ++
      value.compile (ABI.scratch control + 1) ++
        [Instr.store (ABI.scratch control) (ABI.scratch control + 1)])) :
    heapWrites code (address.compile (ABI.scratch control) ++
      value.compile (ABI.scratch control + 1) ++
        [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]).length t =
      {s.eval address} := by
  rw [(store_memory atStore matched.running).2,
    store_address_eq matched hlocals ha hv har]

/-- Both operand evaluations and the final store access only source-heap
addresses. The destination bound is separate from each operand's read bound. -/
theorem store_heapAccesses_below {control locals heapLimit : Nat} {code : Code}
    {s : Source.State w} {t : State w} {address value : Expr}
    (matched : Source.State.Matches heapLimit locals s t) (hlocals : locals ≤ control)
    (ha : address.Bounded locals) (hv : value.Bounded locals)
    (har : address.ReadsBelow heapLimit s.regs s.mem)
    (hvr : value.ReadsBelow heapLimit s.regs s.mem)
    (destination : (s.eval address).toNat < heapLimit)
    (atStore : CodeAt code t.pc (address.compile (ABI.scratch control) ++
      value.compile (ABI.scratch control + 1) ++
        [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]))
    {accessed : Word w}
    (member : accessed ∈ heapAccesses code (address.compile (ABI.scratch control) ++
      value.compile (ABI.scratch control + 1) ++
        [Instr.store (ABI.scratch control) (ABI.scratch control + 1)]).length t) :
    accessed.toNat < heapLimit := by
  have fresh := locals_le_scratch hlocals
  have evaluated := matched.compile_expr ha har fresh
  rw [(store_memory atStore matched.running).1,
    store_address_eq matched hlocals ha hv har,
    Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at member
  rcases member with (addressAccess | valueAccess) | rfl
  · exact expr_access_below matched fresh ha har atStore.append_left.append_left addressAccess
  · have atValue : CodeAt code
        (execBlock (address.compile (ABI.scratch control)) t).pc
        (value.compile (ABI.scratch control + 1)) := by
      rw [execBlock_pc _ t (Expr.compile_linear address (ABI.scratch control))]
      exact atStore.append_left.append_right
    exact expr_access_below evaluated.1 (fresh.trans (Nat.le_succ _)) hv hvr atValue valueAccess
  · exact destination

end Ram.LocalAtomic
