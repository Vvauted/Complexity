/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Arguments.Memory
import Complexity.Computability.Ram.Compiler.ABI.Frame.Memory
import Complexity.Computability.Ram.Compiler.Local.ABI.Basic

/-!
# Heap footprints of the callee-sized call and return blocks

These are footprints of the real machine transitions in arbitrary surrounding
code, not of the callee body. Argument/result evaluation reads the source heap;
the remaining heap accesses save or restore one fixed frame. The saved return
address occupies offset zero and locals occupy offsets `1, ..., locals`.

Calling uses the entry SP, before `advanceLocals`. Returning first executes
`retreatLocals`, and its loads use that restored base, not the return-entry SP.
The exact call-set identity retains modular addresses without a no-wrap
hypothesis. Natural interval bounds require no wrap; the return statements also
use an explicit fitted relation between entry SP and the restored frame base.
No source/target match or saved-value invariant is needed beyond the stated
expression read and register bounds.
-/

namespace Ram.ABI

private theorem split_memory {code left right : Code} {s : State w}
    (atBlock : CodeAt code s.pc (left ++ right))
    (linear : ∀ i ∈ left, i.Linear) (running : s.status = .running) :
    CodeAt code (execBlock left s).pc right ∧
    (execBlock left s).status = .running ∧
    heapAccesses code (left ++ right).length s =
      heapAccesses code left.length s ∪ heapAccesses code right.length (execBlock left s) ∧
    heapWrites code (left ++ right).length s =
      heapWrites code left.length s ∪ heapWrites code right.length (execBlock left s) := by
  refine ⟨?_, (execBlock_status left s linear).trans running, ?_, ?_⟩
  · rw [execBlock_pc left s linear]
    exact atBlock.append_right
  · simpa only [List.length_append] using
      heapAccesses_add (execBlock_exec atBlock.append_left linear running) right.length
  · simpa only [List.length_append] using
      heapWrites_add (execBlock_exec atBlock.append_left linear running) right.length

private theorem no_accesses {code block : Code} {s : State w}
    (atBlock : CodeAt code s.pc block) (linear : ∀ i ∈ block, i.Linear)
    (running : s.status = .running)
    (empty : ∀ i ∈ block, ∀ t : State w, i.heapAccesses t = ∅) :
    heapAccesses code block.length s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  obtain ⟨k, hk, access⟩ :=
    (mem_heapAccesses_execBlock_iff atBlock linear running address).mp member
  rw [empty _ (List.getElem_mem hk)] at access
  exact Finset.notMem_empty _ access

private theorem no_writes_of_no_accesses {code : Code} {steps : Nat} {s : State w}
    (empty : heapAccesses code steps s = ∅) : heapWrites code steps s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  have access := heapWrites_subset_accesses code steps s member
  rw [empty] at access
  exact Finset.notMem_empty _ access

/-- Stack-pointer advancement itself uses only registers. -/
theorem advanceLocals_heapAccesses_eq_empty {code : Code} {control locals : Nat}
    {s : State w} (atBlock : CodeAt code s.pc (advanceLocals control locals))
    (running : s.status = .running) :
    heapAccesses code (advanceLocals control locals).length s = ∅ := by
  apply no_accesses atBlock (advanceLocals_linear control locals) running
  intro i hi t
  simp only [advanceLocals, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

/-- Stack-pointer retreat itself uses only registers. -/
theorem retreatLocals_heapAccesses_eq_empty {code : Code} {control locals : Nat}
    {s : State w} (atBlock : CodeAt code s.pc (retreatLocals control locals))
    (running : s.status = .running) :
    heapAccesses code (retreatLocals control locals).length s = ∅ := by
  apply no_accesses atBlock (retreatLocals_linear control locals) running
  intro i hi t
  simp only [retreatLocals, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> rfl

/-- Exact call-prefix access and write sets. The frame base is the SP before
argument evaluation and before stack advancement. The Word-set identity does
not assume that its addresses do not wrap. -/
theorem callPrefixLocals_footprints {code : Code} {control locals returnPC : Nat}
    {args : List Expr} {s : State w}
    (bufferFit : args.length ≤ control)
    (bounded : ∀ e ∈ args, e.Bounded control)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running) :
    heapAccesses code (callPrefixLocals control locals args returnPC).length s =
      heapAccesses code (evalArgs control 0 args).length s ∪
        ({s.regs (sp control)} ∪ (Finset.range locals).image
          (fun i => arrayAddr (s.regs (sp control)) (i + 1))) ∧
    heapWrites code (callPrefixLocals control locals args returnPC).length s =
      {s.regs (sp control)} ∪ (Finset.range locals).image
        (fun i => arrayAddr (s.regs (sp control)) (i + 1)) := by
  simp only [callPrefixLocals, List.append_assoc] at atBlock ⊢
  obtain ⟨atReturn, readyReturn, accessArgs, writeArgs⟩ :=
    split_memory atBlock (evalArgs_linear control 0 args) running
  obtain ⟨atSave, readySave, accessReturn, writeReturn⟩ :=
    split_memory atReturn (saveReturn_linear control returnPC) readyReturn
  obtain ⟨atInit, readyInit, accessSave, writeSave⟩ :=
    split_memory atSave (saveLocals_linear control locals) readySave
  obtain ⟨atAdvance, readyAdvance, accessInit, writeInit⟩ :=
    split_memory atInit (initLocals_linear control args.length locals) readyInit
  have spArgs : (execBlock (evalArgs control 0 args) s).regs (sp control) =
      s.regs (sp control) :=
    (evalArgs_correct (by simpa using bufferFit) bounded s).control
      (sp control) (by change control < control + 5; omega)
  have initEmpty := initLocals_heapAccesses_eq_empty atInit.append_left readyInit
  have advanceEmpty := advanceLocals_heapAccesses_eq_empty atAdvance readyAdvance
  have savesAccess := saveLocals_heapAccesses atSave.append_left readySave
  have savesWrite := saveLocals_heapWrites atSave.append_left readySave
  have returnLength : (saveReturn control returnPC).length = 2 := rfl
  constructor
  · rw [accessArgs, accessReturn, accessSave, accessInit, initEmpty, advanceEmpty]
    rw [returnLength, saveLocals_length]
    rw [saveReturn_heapAccesses atReturn.append_left readyReturn, savesAccess]
    simp only [saveReturn_sp, spArgs, Finset.union_empty]
  · rw [writeArgs, writeReturn, writeSave, writeInit,
      evalArgs_heapWrites_eq_empty atBlock.append_left running,
      initLocals_heapWrites_eq_empty atInit.append_left readyInit,
      no_writes_of_no_accesses advanceEmpty]
    rw [returnLength, saveLocals_length]
    rw [saveReturn_heapWrites atReturn.append_left readyReturn, savesWrite]
    simp only [saveReturn_sp, spArgs, Finset.empty_union, Finset.union_empty]

private theorem frame_member_bounds {base address : Word w} {locals : Nat}
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (member : address ∈ ({base} ∪ (Finset.range locals).image
      (fun i => arrayAddr base (i + 1)))) :
    base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + frameSize locals := by
  rcases Finset.mem_union.mp member with zero | slot
  · have eq : address = base := Finset.mem_singleton.mp zero
    subst address
    simp only [frameSize]
    omega
  · have slotFit : base.toNat + locals < 2 ^ w := by
      unfold frameSize at fits
      omega
    obtain ⟨lower, upper⟩ := (mem_slot_image_iff slotFit).mp slot
    unfold frameSize
    omega

/-- Calls read only the declared source heap or the frame that they save.
The source heap need not be disjoint from the frame for this disjunctive bound. -/
theorem callPrefixLocals_heapAccesses_bounded
    {code : Code} {control locals returnPC heapLimit : Nat} {args : List Expr} {s : State w}
    (localFit : locals ≤ control) (countFit : args.length ≤ locals)
    (bounded : ∀ e ∈ args, e.Bounded control)
    (reads : ∀ e ∈ args, e.ReadsBelow heapLimit s.regs s.mem)
    (fits : (s.regs (sp control)).toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running) {address : Word w}
    (member : address ∈ heapAccesses code
      (callPrefixLocals control locals args returnPC).length s) :
    address.toNat < heapLimit ∨
      (s.regs (sp control)).toNat ≤ address.toNat ∧
        address.toNat < (s.regs (sp control)).toNat + frameSize locals := by
  rw [(callPrefixLocals_footprints (countFit.trans localFit) bounded atBlock running).1,
    Finset.mem_union] at member
  rcases member with argument | frame
  · exact Or.inl (evalArgs_heapAccesses_below bounded reads
      atBlock.append_left.append_left.append_left.append_left running argument)
  · exact Or.inr (frame_member_bounds fits frame)

/-- Every actual call-prefix write is in its one fixed frame. -/
theorem callPrefixLocals_heapWrites_bounded
    {code : Code} {control locals returnPC : Nat} {args : List Expr} {s : State w}
    (localFit : locals ≤ control) (countFit : args.length ≤ locals)
    (bounded : ∀ e ∈ args, e.Bounded control)
    (fits : (s.regs (sp control)).toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running) {address : Word w}
    (member : address ∈ heapWrites code
      (callPrefixLocals control locals args returnPC).length s) :
    (s.regs (sp control)).toNat ≤ address.toNat ∧
      address.toNat < (s.regs (sp control)).toNat + frameSize locals := by
  rw [(callPrefixLocals_footprints (countFit.trans localFit) bounded atBlock running).2]
    at member
  exact frame_member_bounds fits member

private theorem returnPrefix_memory {code : Code} {control locals : Nat}
    {result : Expr} {s : State w}
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    let evaluated := execBlock (result.compile (scratch control)) s
    let buffered := execBlock [.move (rv control) (scratch control)] evaluated
    let retreated := execBlock (retreatLocals control locals) buffered
    let addressed := execBlock [.load (ra control) (sp control)] retreated
    (locals ≤ control →
      heapAccesses code (returnPrefixLocals control locals result).length s =
        heapAccesses code (result.compile (scratch control)).length s ∪
          ({retreated.regs (sp control)} ∪ (Finset.range locals).image
            (fun i => arrayAddr (addressed.regs (sp control)) (i + 1)))) ∧
    heapWrites code (returnPrefixLocals control locals result).length s = ∅ := by
  dsimp only
  simp only [returnPrefixLocals, returnPrefixResultsLocals, evalResults_singleton,
    List.append_assoc] at atBlock ⊢
  obtain ⟨atMove, readyMove, accessExpr, writeExpr⟩ :=
    split_memory atBlock (result.compile_linear (scratch control)) running
  obtain ⟨atRetreat, readyRetreat, accessMove, writeMove⟩ :=
    split_memory (left := [.move (rv control) (scratch control)]) atMove
      (by simp [Instr.Linear]) readyMove
  obtain ⟨atLoad, readyLoad, accessRetreat, writeRetreat⟩ :=
    split_memory atRetreat (retreatLocals_linear control locals) readyRetreat
  obtain ⟨atRestore, readyRestore, accessLoad, writeLoad⟩ :=
    split_memory (left := [.load (ra control) (sp control)]) atLoad
      (by simp [Instr.Linear]) readyLoad
  have moveEmpty : heapAccesses code [Instr.move (rv control) (scratch control)].length
      (execBlock (result.compile (scratch control)) s) = ∅ := by
    rw [List.length_singleton, heapAccesses_one,
      stepHeapAccesses_of_fetch readyMove atMove.head]
    rfl
  have retreatEmpty := retreatLocals_heapAccesses_eq_empty atRetreat.append_left readyRetreat
  constructor
  · intro localFit
    rw [accessExpr, accessMove, accessRetreat, accessLoad, moveEmpty, retreatEmpty,
      restoreLocals_length, restoreLocals_heapAccesses localFit atRestore readyRestore,
      List.length_singleton, heapAccesses_one,
      stepHeapAccesses_of_fetch readyLoad atLoad.head]
    simp only [Instr.heapAccesses, Finset.empty_union]
  · rw [writeExpr, writeMove, writeRetreat, writeLoad,
      Expr.compile_heapWrites_eq_empty atBlock.append_left running,
      no_writes_of_no_accesses moveEmpty, no_writes_of_no_accesses retreatEmpty,
      restoreLocals_length, restoreLocals_heapWrites atRestore readyRestore,
      List.length_singleton, heapWrites_one,
      stepHeapWrites_of_fetch readyLoad atLoad.head]
    simp only [Instr.heapWrites, Finset.empty_union]

/-- A return prefix executes no stores, independently of the validity of the
saved frame or expression. This is an actual write-set statement, not an
inference from final heap equality. -/
theorem returnPrefixLocals_heapWrites_eq_empty {code : Code} {control locals : Nat}
    {result : Expr} {s : State w}
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    heapWrites code (returnPrefixLocals control locals result).length s = ∅ :=
  (returnPrefix_memory atBlock running).2

/-- The exact return access set consists of result-expression reads and the
frame at `base`. The return-entry SP is one whole frame above this base. -/
theorem returnPrefixLocals_heapAccesses {code : Code} {control locals : Nat}
    {result : Expr} {s : State w} {base : Word w}
    (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) :
    heapAccesses code (returnPrefixLocals control locals result).length s =
      heapAccesses code (result.compile (scratch control)).length s ∪
        ({base} ∪ (Finset.range locals).image (fun i => arrayAddr base (i + 1))) := by
  let evaluated := execBlock (result.compile (scratch control)) s
  let buffered := execBlock [.move (rv control) (scratch control)] evaluated
  let retreated := execBlock (retreatLocals control locals) buffered
  let addressed := execBlock [.load (ra control) (sp control)] retreated
  have scratchFit : control ≤ scratch control := by unfold scratch; omega
  have correct := Expr.compile_correct (bounded.mono (localFit.trans scratchFit)) s
  have spEvaluated : evaluated.regs (sp control) = s.regs (sp control) :=
    correct.below (sp control) (by change control < 2 * control + 5; omega)
  have spBuffered : buffered.regs (sp control) = s.regs (sp control) := by
    have ne : sp control ≠ rv control := by simp [sp, rv]
    simpa only [buffered, execBlock_cons, execBlock_nil, execInstr,
      State.next_regs, State.setReg_ne _ _ _ _ ne] using spEvaluated
  have spRetreated : retreated.regs (sp control) = base :=
    retreatLocals_sp control locals buffered base (by rw [spBuffered]; exact stack) fits
  have spAddressed : addressed.regs (sp control) = base := by
    have ne : sp control ≠ ra control := by simp [sp, ra]
    simpa only [addressed, execBlock_cons, execBlock_nil, execInstr,
      State.next_regs, State.setReg_ne _ _ _ _ ne] using spRetreated
  have footprint := (returnPrefix_memory atBlock running).1 localFit
  change heapAccesses code (returnPrefixLocals control locals result).length s =
    heapAccesses code (result.compile (scratch control)).length s ∪
      ({retreated.regs (sp control)} ∪ (Finset.range locals).image
        (fun i => arrayAddr (addressed.regs (sp control)) (i + 1))) at footprint
  simpa only [spRetreated, spAddressed] using footprint

/-- A return prefix reads only the source heap or the original saved frame,
whose base is recovered by the real retreat instructions. -/
theorem returnPrefixLocals_heapAccesses_bounded
    {code : Code} {control locals heapLimit : Nat} {result : Expr} {s : State w}
    {base : Word w} (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (returnPrefixLocals control locals result))
    (running : s.status = .running) {address : Word w}
    (member : address ∈ heapAccesses code
      (returnPrefixLocals control locals result).length s) :
    address.toNat < heapLimit ∨
      base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + frameSize locals := by
  rw [returnPrefixLocals_heapAccesses localFit bounded stack fits atBlock running,
    Finset.mem_union] at member
  rcases member with expression | frame
  · have scratchFit : control ≤ scratch control := by unfold scratch; omega
    exact Or.inl (Expr.compile_heapAccesses_below
      (bounded.mono (localFit.trans scratchFit)) reads
      atBlock.append_left.append_left.append_left.append_left running expression)
  · exact Or.inr (frame_member_bounds fits frame)

/-- The final indirect jump adds no heap access or write. Its target need not
be correct for this one-step footprint identity. No later callee/caller code is
included in the observation horizon. -/
theorem returnCodeLocals_footprints {code : Code} {control locals : Nat}
    {result : Expr} {s : State w}
    (atBlock : CodeAt code s.pc (returnCodeLocals control locals result))
    (running : s.status = .running) :
    heapAccesses code (returnCodeLocals control locals result).length s =
      heapAccesses code (returnPrefixLocals control locals result).length s ∧
    heapWrites code (returnCodeLocals control locals result).length s = ∅ := by
  unfold returnCodeLocals at atBlock ⊢
  obtain ⟨atJump, readyJump, accesses, writes⟩ :=
    split_memory atBlock (returnPrefixLocals_linear control locals result) running
  constructor
  · rw [accesses, List.length_singleton, heapAccesses_one,
      stepHeapAccesses_of_fetch readyJump atJump.head]
    exact Finset.union_empty _
  · rw [writes, returnPrefixLocals_heapWrites_eq_empty atBlock.append_left running,
      List.length_singleton, heapWrites_one, stepHeapWrites_of_fetch readyJump atJump.head]
    rfl

/-- The complete return code, including its last `jumpReg`, writes no heap. -/
theorem returnCodeLocals_heapWrites_eq_empty {code : Code} {control locals : Nat}
    {result : Expr} {s : State w}
    (atBlock : CodeAt code s.pc (returnCodeLocals control locals result))
    (running : s.status = .running) :
    heapWrites code (returnCodeLocals control locals result).length s = ∅ :=
  (returnCodeLocals_footprints atBlock running).2

/-- The frame/source-heap bound extends through the return jump itself. -/
theorem returnCodeLocals_heapAccesses_bounded
    {code : Code} {control locals heapLimit : Nat} {result : Expr} {s : State w}
    {base : Word w} (localFit : locals ≤ control) (bounded : result.Bounded locals)
    (reads : result.ReadsBelow heapLimit s.regs s.mem)
    (stack : (s.regs (sp control)).toNat = base.toNat + frameSize locals)
    (fits : base.toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (returnCodeLocals control locals result))
    (running : s.status = .running) {address : Word w}
    (member : address ∈ heapAccesses code (returnCodeLocals control locals result).length s) :
    address.toNat < heapLimit ∨
      base.toNat ≤ address.toNat ∧ address.toNat < base.toNat + frameSize locals := by
  rw [(returnCodeLocals_footprints atBlock running).1] at member
  exact returnPrefixLocals_heapAccesses_bounded localFit bounded reads stack fits
    atBlock.append_left running member

/-- When the fixed frame starts above the source heap, every real intermediate
state of call setup preserves that heap. Initial expression reads need no bound
for this write-only conclusion. -/
theorem callPrefixLocals_prefix_heap
    {code : Code} {control locals returnPC heapLimit k : Nat} {args : List Expr}
    {s current : State w} (localFit : locals ≤ control) (countFit : args.length ≤ locals)
    (bounded : ∀ e ∈ args, e.Bounded control)
    (heap : heapLimit ≤ (s.regs (sp control)).toNat)
    (fits : (s.regs (sp control)).toNat + frameSize locals < 2 ^ w)
    (atBlock : CodeAt code s.pc (callPrefixLocals control locals args returnPC))
    (running : s.status = .running)
    (hk : k ≤ (callPrefixLocals control locals args returnPC).length)
    (execution : Exec code k s current) : HeapEqBelow heapLimit s.mem current.mem := by
  apply execution.prefix_heapEqBelow_of_writes_above hk heapLimit
  intro address member
  exact heap.trans (callPrefixLocals_heapWrites_bounded localFit countFit bounded fits
    atBlock running member).1

/-- Through the complete return block, including its final jump, every actual
prefix preserves the entire heap because the actual write set is empty. -/
theorem returnCodeLocals_prefix_mem {code : Code} {control locals k : Nat}
    {result : Expr} {s current : State w}
    (atBlock : CodeAt code s.pc (returnCodeLocals control locals result))
    (running : s.status = .running) (hk : k ≤ (returnCodeLocals control locals result).length)
    (execution : Exec code k s current) : current.mem = s.mem :=
  execution.prefix_mem_eq_of_heapWrites_empty hk
    (returnCodeLocals_heapWrites_eq_empty atBlock running)

end Ram.ABI
