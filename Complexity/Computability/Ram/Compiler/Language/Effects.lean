/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Lowering
import Complexity.Computability.Ram.Source.Effects

/-!
# Shared-state preservation of scalar lowering

Scalar lowering emits local assignments, branches, sequences and actual calls.
Its emitted function bodies contain no shared-state writes. The generic source
effect theorem therefore applies to every completed invocation, including
recursive calls, rather than requiring a preservation proof for each algorithm.

The statement lemma retains its continuation premise: arbitrary appended IR
need not preserve shared state. These syntactic facts establish neither source
termination nor a cost bound; they apply to the same lowered program and its
existing execution relation.
-/

namespace Ram.LanguageCompiler

open Complexity.Language

/-- Materializing a scalar primitive changes only a local result slot. -/
theorem lowerPrim_noSharedWrites (layout : RegisterMap Γ) (dst : Reg) (prim : Prim Γ τ) :
    (lowerPrim layout dst prim).NoSharedWrites := by
  cases τ <;> trivial

/-- Returning a scalar value writes its local result field, or no field for Unit. -/
theorem lowerReturn_noSharedWrites (layout : RegisterMap Γ) (resultSlot : Reg)
    (atom : Atom Γ τ) : (lowerReturn layout resultSlot atom).NoSharedWrites := by
  cases τ <;> trivial

/-- The core lowering only writes local values and the private return flag.
Actual callees are covered by the separate program-wide body condition. -/
theorem lowerStmtCore_noSharedWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot flag : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) :
    (lowerStmtCore layout next resultSlot flag stmt).NoSharedWrites := by
  induction stmt generalizing next resultSlot flag with
  | skip => trivial
  | letPrim value body ih =>
    exact ⟨lowerPrim_noSharedWrites layout next value, ih _ _ _ _⟩
  | call fn args body ih =>
    exact ⟨trivial, ih _ _ _ _⟩
  | seq first second firstIH secondIH =>
    exact ⟨firstIH _ _ _ _, trivial, secondIH _ _ _ _⟩
  | ite test yes no yesIH noIH =>
    exact ⟨yesIH _ _ _ _, noIH _ _ _ _⟩
  | ret value => exact ⟨lowerReturn_noSharedWrites layout resultSlot value, trivial⟩

/-- Scalar statement lowering retains the no-shared-writes condition of its
normal continuation. The private return flag guards that continuation without
adding a shared-state write. -/
theorem lowerStmt_noSharedWrites {signatures : List Signature} {Γ : List Ty} {result : Ty}
    (layout : RegisterMap Γ) (next resultSlot : Reg)
    (stmt : Complexity.Language.Stmt signatures Γ result) (continuation : Ram.Stmt)
    (condition : continuation.NoSharedWrites) :
    (lowerStmt layout next resultSlot stmt continuation).NoSharedWrites := by
  exact ⟨trivial, lowerStmtCore_noSharedWrites _ _ _ _ _, trivial, condition⟩

/-- Every lowered scalar function body satisfies the shared-write condition. -/
theorem lowerBody_noSharedWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures) (fn : Fin signatures.length) :
    (lowerBody program fn).NoSharedWrites :=
  lowerStmt_noSharedWrites _ _ _ _ _ trivial

/-- All actual entries in the lowered function table have no shared writes.
This single condition covers recursive and mutually recursive target calls. -/
theorem lowerProgram_noSharedWrites {signatures : List Signature}
    (program : Complexity.Language.Program signatures) :
    ∀ f ∈ lowerProgram program, f.body.NoSharedWrites := by
  intro f member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact lowerBody_noSharedWrites program index

end Ram.LanguageCompiler
