/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Compiler.Language.Control
import Complexity.Computability.Ram.Source.Effects

/-!
# Heap and stream effects of lowering

The source fragment without heap writes lowers to local assignments, reads,
branches, sequences and actual calls. Buffer stores are explicitly excluded
from its preservation theorem. The generic source effect theorem applies when
every actual function body satisfies this condition, including recursive calls.
All supported source operations are free of input/output stream operations,
including buffer writes. Their generated program therefore satisfies the
separate stream-preservation condition without a read-only premise.

The statement lemma retains its continuation premise: arbitrary appended IR
need not preserve shared state. These syntactic facts establish neither source
termination nor a cost bound; they apply to the same lowered program and its
existing execution relation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- The source fragment with no direct heap writes. Calls additionally require
the same property for the complete program's bodies when using a frame theorem. -/
def NoHeapWrites {signatures : List Signature} {Γ : List Ty} {result : Ty} :
    Complexity.Language.Stmt signatures Γ result → Prop
  | .skip | .assign .. | .ret _ => True
  | .letPrim _ body | .read _ _ body | .slice _ _ _ body | .call _ _ body =>
      NoHeapWrites body
  | .write .. => False
  | .seq first second => NoHeapWrites first ∧ NoHeapWrites second
  | .ite _ yes no => NoHeapWrites yes ∧ NoHeapWrites no

/-- Ordered field materialization only changes its local destinations. -/
theorem copyFields_noSharedWrites (dst : Reg) (fields : List Expr) :
    (copyFields dst fields).NoSharedWrites := by
  induction fields generalizing dst with
  | nil => trivial
  | cons expr rest ih =>
      cases rest with
      | nil => trivial
      | cons next rest => exact ⟨trivial, ih (dst + 1)⟩

/-- Materializing a primitive changes only its local result fields. -/
theorem lowerPrim_noSharedWrites (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    (lowerPrim layout dst prim).NoSharedWrites := by
  cases τ with
  | nat | bool | unit => trivial
  | buffer kind =>
      cases prim with
      | atom atom => exact copyFields_noSharedWrites dst (atomExprs layout atom)

/-- Reassigning a local does not write through a buffer or change either stream. -/
theorem lowerAssign_noSharedWrites (layout : RegisterMap Γ) (target : Var Γ τ)
    (value : Prim Γ τ) : (lowerAssign layout target value).NoSharedWrites :=
  lowerPrim_noSharedWrites layout (RegisterMap.base layout target) value

/-- Returning a value writes only its local result fields, or none for Unit. -/
theorem lowerReturn_noSharedWrites (layout : RegisterMap Γ) (resultSlot : Reg)
    (atom : Atom Γ τ) : (lowerReturn layout resultSlot atom).NoSharedWrites :=
  copyFields_noSharedWrites resultSlot (atomExprs layout atom)

/-- A source body without heap writes changes only local values and its private
return flag. Actual callees have a separate program-wide body condition. -/
theorem lowerStmtCore_noSharedWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) :
    NoHeapWrites stmt → (lowerStmtCore layout next resultSlot flag stmt).NoSharedWrites := by
  induction stmt generalizing next resultSlot flag with
  | skip => intro _; trivial
  | assign target value => intro _; exact lowerAssign_noSharedWrites layout target value
  | letPrim value body ih =>
    intro condition
    exact ⟨lowerPrim_noSharedWrites layout next value, ih _ _ _ _ condition⟩
  | read buffer index body ih =>
    intro condition
    exact ⟨trivial, ih _ _ _ _ condition⟩
  | write buffer index value => exact False.elim
  | slice buffer offset length body ih =>
    intro condition
    exact ⟨⟨trivial, trivial⟩, ih _ _ _ _ condition⟩
  | call fn args body ih =>
    intro condition
    exact ⟨trivial, ih _ _ _ _ condition⟩
  | seq first second firstIH secondIH =>
    intro condition
    exact ⟨firstIH _ _ _ _ condition.1, trivial, secondIH _ _ _ _ condition.2⟩
  | ite test yes no yesIH noIH =>
    intro condition
    exact ⟨yesIH _ _ _ _ condition.1, noIH _ _ _ _ condition.2⟩
  | ret value => intro _; exact ⟨lowerReturn_noSharedWrites layout resultSlot value, trivial⟩

/-- A read-only source statement retains the no-shared-writes condition of its
normal continuation. The return flag adds no shared-state write. -/
theorem lowerStmt_noSharedWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) (continuation : Ram.Stmt)
    (condition : continuation.NoSharedWrites) (sourceCondition : NoHeapWrites stmt) :
    (lowerStmt layout next resultSlot stmt continuation).NoSharedWrites := by
  exact ⟨trivial, lowerStmtCore_noSharedWrites _ _ _ _ _ sourceCondition, trivial, condition⟩

/-- A read-only function body satisfies the target shared-write condition. -/
theorem lowerBody_noSharedWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length)
    (condition : NoHeapWrites (program.body fn)) :
    (lowerBody program fn).NoSharedWrites :=
  ⟨trivial, lowerStmtCore_noSharedWrites _ _ _ _ _ condition⟩

/-- A complete read-only function table has no shared writes. This condition
covers actual recursive and mutually recursive target calls. -/
theorem lowerProgram_noSharedWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures)
    (condition : ∀ fn, NoHeapWrites (program.body fn)) :
    ∀ f ∈ lowerProgram program, f.body.NoSharedWrites := by
  intro f member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact lowerBody_noSharedWrites program index (condition index)

/-- Field copies never consume input or emit output. -/
theorem copyFields_noIOWrites (dst : Reg) (fields : List Expr) :
    (copyFields dst fields).NoIOWrites := by
  induction fields generalizing dst with
  | nil => trivial
  | cons expr rest ih =>
      cases rest with
      | nil => trivial
      | cons next rest => exact ⟨trivial, ih (dst + 1)⟩

/-- Primitive materialization performs no stream operation. -/
theorem lowerPrim_noIOWrites (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    (lowerPrim layout dst prim).NoIOWrites := by
  cases τ with
  | nat | bool | unit => trivial
  | buffer kind =>
      cases prim with
      | atom atom => exact copyFields_noIOWrites dst (atomExprs layout atom)

/-- Updating any local value leaves the input and output streams untouched. -/
theorem lowerAssign_noIOWrites (layout : RegisterMap Γ) (target : Var Γ τ)
    (value : Prim Γ τ) : (lowerAssign layout target value).NoIOWrites :=
  lowerPrim_noIOWrites layout (RegisterMap.base layout target) value

/-- Returning actual value fields does not write to an output stream. -/
theorem lowerReturn_noIOWrites (layout : RegisterMap Γ) (resultSlot : Reg)
    (atom : Atom Γ τ) : (lowerReturn layout resultSlot atom).NoIOWrites :=
  copyFields_noIOWrites resultSlot (atomExprs layout atom)

/-- Reading a buffer cell is a heap load, not an input-stream operation. -/
theorem lowerRead_noIOWrites (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (index : Atom Γ .nat) :
    (lowerRead layout dst buffer index).NoIOWrites := trivial

/-- Writing a buffer cell changes the heap, not either stream. -/
theorem lowerWrite_noIOWrites (layout : RegisterMap Γ) (buffer : Atom Γ (.buffer kind))
    (index : Atom Γ .nat) (value : Atom Γ kind.toTy) :
    (lowerWrite layout buffer index value).NoIOWrites := trivial

/-- Constructing a borrowed descriptor only assigns its local fields. -/
theorem lowerSlice_noIOWrites (layout : RegisterMap Γ) (dst : Reg)
    (buffer : Atom Γ (.buffer kind)) (offset length : Atom Γ .nat) :
    (lowerSlice layout dst buffer offset length).NoIOWrites := ⟨trivial, trivial⟩

/-- Every source body lowers without stream operations. Actual callees are
covered by the same condition for the generated function table. -/
theorem lowerStmtCore_noIOWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) :
    (lowerStmtCore layout next resultSlot flag stmt).NoIOWrites := by
  induction stmt generalizing next resultSlot flag with
  | skip => trivial
  | assign target value => exact lowerAssign_noIOWrites layout target value
  | letPrim value body ih => exact ⟨lowerPrim_noIOWrites _ _ _, ih _ _ _ _⟩
  | read buffer index body ih => exact ⟨lowerRead_noIOWrites _ _ _ _, ih _ _ _ _⟩
  | write buffer index value => exact lowerWrite_noIOWrites _ _ _ _
  | slice buffer offset length body ih =>
      exact ⟨lowerSlice_noIOWrites _ _ _ _ _, ih _ _ _ _⟩
  | call fn args body ih => exact ⟨trivial, ih _ _ _ _⟩
  | seq first second firstIH secondIH => exact ⟨firstIH _ _ _ _, trivial, secondIH _ _ _ _⟩
  | ite test yes no yesIH noIH => exact ⟨yesIH _ _ _ _, noIH _ _ _ _⟩
  | ret value => exact ⟨lowerReturn_noIOWrites _ _ _, trivial⟩

/-- The generic wrapper preserves a stream-free normal continuation. -/
theorem lowerStmt_noIOWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) (continuation : Ram.Stmt)
    (condition : continuation.NoIOWrites) :
    (lowerStmt layout next resultSlot stmt continuation).NoIOWrites :=
  ⟨trivial, lowerStmtCore_noIOWrites _ _ _ _ _, trivial, condition⟩

/-- Each generated function body is stream-free, including bodies that store
through borrowed buffers. -/
theorem lowerBody_noIOWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerBody program fn).NoIOWrites :=
  ⟨trivial, lowerStmtCore_noIOWrites _ _ _ _ _⟩

/-- The actual generated table satisfies the stream-preservation premise for
all calls, including recursive calls. No heap-preservation claim is made. -/
theorem lowerProgram_noIOWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures) :
    ∀ f ∈ lowerProgram program, f.body.NoIOWrites := by
  intro f member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact lowerBody_noIOWrites program index

/-- Sequential copying writes exactly its consecutive destination fields.
This concerns local destinations, not the expressions' possible heap reads. -/
theorem copyFields_writtenRegs (dst : Reg) (fields : List Expr) :
    (copyFields dst fields).writtenRegs = {r | r ∈ List.range' dst fields.length} := by
  induction fields generalizing dst with
  | nil =>
      ext r
      simp [copyFields, Ram.Stmt.writtenRegs]
  | cons expr rest ih =>
      cases rest with
      | nil =>
          ext r
          simp [copyFields, Ram.Stmt.writtenRegs, List.range'_succ]
      | cons next rest =>
          rw [copyFields, Ram.Stmt.writtenRegs, ih]
          ext r
          simp [Ram.Stmt.writtenRegs, List.range'_succ]

/-- A primitive writes only its actual destination tuple, including the empty
tuple for Unit. Register effects do not require a value-range premise. -/
theorem lowerPrim_writtenRegs (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    (lowerPrim layout dst prim).writtenRegs = {r | r ∈ valueRegs τ dst} := by
  cases τ with
  | nat | bool | unit =>
      ext r
      simp [lowerPrim, Ram.Stmt.writtenRegs, valueRegs, List.range'_succ]
  | buffer kind =>
      cases prim with
      | atom atom =>
          simp only [lowerPrim, copyFields_writtenRegs, atomExprs_length, valueRegs]

/-- Returning a value writes its result region, without touching any other
caller-local register. The return flag is assigned separately by the core. -/
theorem lowerReturn_writtenRegs (layout : RegisterMap Γ) (resultSlot : Reg)
    (atom : Atom Γ τ) :
    (lowerReturn layout resultSlot atom).writtenRegs = {r | r ∈ valueRegs τ resultSlot} := by
  simp only [lowerReturn, copyFields_writtenRegs, atomExprs_length, valueRegs]

/-- A private register below fresh allocation is outside every possible local
write of the lowered core. Existing-variable assignment uses the regular layout;
calls only receive their result fields after restoring caller locals. Neither
heap preservation nor extra reset instructions are needed. -/
theorem lowerStmtCore_not_mem_writtenRegs {signatures : List Signature} {Γ : List Ty}
    {result : Ty} (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) {r : Reg}
    (regular : RegisterMap.Regular layout) (bounded : layout.Bounded next)
    (avoids : layout.Avoids r) (before : r < next)
    (outsideResult : r ∉ valueRegs result resultSlot) (differentFlag : r ≠ flag) :
    r ∉ (lowerStmtCore layout next resultSlot flag stmt).writtenRegs := by
  revert regular bounded avoids before outsideResult differentFlag
  induction stmt generalizing next resultSlot flag with
  | skip =>
      intros
      simp [lowerStmtCore, Ram.Stmt.writtenRegs]
  | assign target value =>
      intro regular bounded avoids before outsideResult differentFlag
      rw [lowerStmtCore, lowerAssign, lowerPrim_writtenRegs]
      exact regular.not_mem_valueRegs_of_avoids avoids target
  | letPrim value body ih =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨?_, ?_⟩
      · rw [lowerPrim_writtenRegs]
        exact flag_not_mem_valueRegs_of_lt _ next r before
      · exact ih _ _ _ _ (regular.extend bounded) (RegisterMap.extend_bounded bounded)
          (avoids.extend before) (Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))
          outsideResult differentFlag
  | read buffer index body ih =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨Nat.ne_of_lt before, ?_⟩
      exact ih _ _ _ _ (regular.extend bounded) (RegisterMap.extend_bounded bounded)
        (avoids.extend before) (Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))
        outsideResult differentFlag
  | write buffer index value =>
      intros
      simp [lowerStmtCore, lowerWrite, Ram.Stmt.writtenRegs]
  | slice buffer offset length body ih =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨not_or.mpr ⟨Nat.ne_of_lt before,
        Nat.ne_of_lt (Nat.lt_trans before (Nat.lt_succ_self next))⟩, ?_⟩
      exact ih _ _ _ _ (regular.extend bounded) (RegisterMap.extend_bounded bounded)
        (avoids.extend before) (Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))
        outsideResult differentFlag
  | call fn args body ih =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨flag_not_mem_valueRegs_of_lt _ next r before, ?_⟩
      exact ih _ _ _ _ (regular.extend bounded) (RegisterMap.extend_bounded bounded)
        (avoids.extend before) (Nat.lt_of_lt_of_le before (Nat.le_add_right _ _))
        outsideResult differentFlag
  | seq first second firstIH secondIH =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨firstIH _ _ _ _ regular bounded avoids before
        outsideResult differentFlag, not_or.mpr ⟨?_, ?_⟩⟩
      · exact fun impossible => impossible
      · exact secondIH _ _ _ _ regular bounded avoids before outsideResult differentFlag
  | ite test yes no yesIH noIH =>
      intro regular bounded avoids before outsideResult differentFlag
      exact not_or.mpr ⟨yesIH _ _ _ _ regular bounded avoids before outsideResult differentFlag,
        noIH _ _ _ _ regular bounded avoids before outsideResult differentFlag⟩
  | ret value =>
      intro regular bounded avoids before outsideResult differentFlag
      refine not_or.mpr ⟨?_, differentFlag⟩
      simpa only [lowerReturn_writtenRegs] using outsideResult

/-- A completed lowered core preserves the same private register by the
existing safe-execution frame theorem. This also applies to an erased measured
execution; the proof adds no runtime work or cost premise. -/
theorem lowerStmtCore_regs_eq {signatures : List Signature} {Γ : List Ty} {result : Ty}
    {program : Ram.Program} {heapLimit depth : Nat} {layout : RegisterMap Γ}
    {next resultSlot flag r : Reg} {stmt : Complexity.Language.Stmt signatures Γ result}
    {entry finish : Source.State w}
    (execution : Source.SafeExec program heapLimit depth
      (lowerStmtCore layout next resultSlot flag stmt) entry finish)
    (regular : RegisterMap.Regular layout) (bounded : layout.Bounded next)
    (avoids : layout.Avoids r) (before : r < next)
    (outsideResult : r ∉ valueRegs result resultSlot) (differentFlag : r ≠ flag) :
    finish.regs r = entry.regs r :=
  execution.regs_eq_of_not_mem_writtenRegs
    (lowerStmtCore_not_mem_writtenRegs layout next resultSlot flag stmt
      regular bounded avoids before outsideResult differentFlag)

end Ram.LanguageCompiler
