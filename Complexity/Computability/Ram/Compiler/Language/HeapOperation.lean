/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Heap
import Complexity.Computability.Ram.Compiler.Local.Measured.Basic

/-!
# Executing represented source heap operations

Successful source reads and writes correspond to ordinary RAM loads and stores.
The runtime base, index and stored value are arbitrary expressions; their safe
evaluation and correspondence are proof premises. The mathematical placement is
not an instruction operand, an object table or an uncharged runtime lookup.

Each rule gives the exact same endpoint for safe and measured execution and
retains the complete shared-heap representation. Counts are the existing local
compiler's actual statement sizes, including operand evaluation. The rules are
uniform in the cell type and permit the aliases admitted by `HeapRep`.

These are successful-operation bridges, not new source syntax or a second
semantics. They implement neither source error outcomes nor runtime validity
checks; a successful source operation is an explicit premise.
-/

namespace Ram.LanguageCompiler.HeapRep

open Complexity.Language

variable {w heapLimit depth control : Nat} {program : Ram.Program}
variable {placement : Nat → Word w} {heap finish : Complexity.Language.Heap}
variable {target : Source.State w} {τ : CellTy} {buffer : Buffer τ}
variable {index : Nat} {value : CellValue τ}

/-- A successful source read executes a real indexed assignment, returning the
exact cell encoding and preserving the complete heap at the same endpoint.
The destination may coincide with an operand register: operands are evaluated
in the entry state before the assignment. -/
theorem read_assign (represented : HeapRep placement heapLimit heap target)
    (read : heap.read buffer index = .ok value) (dst : Reg) (base offset : Expr)
    (baseReads : base.ReadsBelow heapLimit target.regs target.mem)
    (offsetReads : offset.ReadsBelow heapLimit target.regs target.mem)
    (baseValue : target.eval base = (bufferRef placement buffer).base)
    (indexValue : target.eval offset = BitVec.ofNat w index) :
    let received := target.setReg dst (cellWord w value)
    Source.SafeExec program heapLimit depth (.assign dst (Expr.index base offset))
        target received ∧
      Source.LocalMeasuredExec control program heapLimit depth
        (.assign dst (Expr.index base offset))
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (.assign dst (Expr.index base offset))) target received ∧
      HeapRep placement heapLimit heap received ∧ cellToNat value < 2 ^ w := by
  dsimp only
  obtain ⟨cell, destination, fits⟩ := represented.read read
  have address : target.eval (.bin .add base offset) =
      arrayAddr (bufferRef placement buffer).base index := by
    change target.eval base + target.eval offset =
      (bufferRef placement buffer).base + BitVec.ofNat w index
    rw [baseValue, indexValue]
  have reads : (Expr.index base offset).ReadsBelow heapLimit target.regs target.mem := by
    refine ⟨⟨baseReads, offsetReads⟩, ?_⟩
    change (target.eval (.bin .add base offset)).toNat < heapLimit
    rw [address]
    exact destination
  have actual : target.eval (Expr.index base offset) = cellWord w value := by
    change target.mem (target.eval (.bin .add base offset)) = cellWord w value
    rw [address]
    exact cell
  have execution : Source.LocalMeasuredExec control program heapLimit depth
      (.assign dst (Expr.index base offset))
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.assign dst (Expr.index base offset))) target
      (target.setReg dst (cellWord w value)) := by
    rw [← actual]
    exact .assign reads
  refine ⟨execution.erase, execution, ?_, fits⟩
  simpa only [Source.State.setRegs_singleton] using
    represented.setRegs [dst] [cellWord w value]

/-- A successful source write executes the supplied address and value
expressions, retaining the actual updated complete heap, including overlapping
views. Exact encoding and the source cell range exclude silent word truncation.
Both execution judgments use the compiler-derived size of this same store. -/
theorem write_store (represented : HeapRep placement heapLimit heap target)
    (written : heap.write buffer index value = .ok finish)
    (valueFits : cellToNat value < 2 ^ w) (base offset stored : Expr)
    (baseReads : base.ReadsBelow heapLimit target.regs target.mem)
    (offsetReads : offset.ReadsBelow heapLimit target.regs target.mem)
    (valueReads : stored.ReadsBelow heapLimit target.regs target.mem)
    (baseValue : target.eval base = (bufferRef placement buffer).base)
    (indexValue : target.eval offset = BitVec.ofNat w index)
    (storedValue : target.eval stored = cellWord w value) :
    let updated := target.setMem (arrayAddr (bufferRef placement buffer).base index)
      (cellWord w value)
    Source.SafeExec program heapLimit depth (.store (.bin .add base offset) stored)
        target updated ∧
      Source.LocalMeasuredExec control program heapLimit depth
        (.store (.bin .add base offset) stored)
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
          (.store (.bin .add base offset) stored)) target updated ∧
      HeapRep placement heapLimit finish updated := by
  dsimp only
  obtain ⟨values, found, extent, bound, _⟩ :=
    Complexity.Language.Heap.write_eq_ok_iff.mp written
  have readable := Complexity.Language.Heap.read_eq found extent bound
  have destination := (represented.read readable).2.1
  have address : target.eval (.bin .add base offset) =
      arrayAddr (bufferRef placement buffer).base index := by
    change target.eval base + target.eval offset =
      (bufferRef placement buffer).base + BitVec.ofNat w index
    rw [baseValue, indexValue]
  have targetBound : (target.eval (.bin .add base offset)).toNat < heapLimit := by
    rw [address]
    exact destination
  have execution : Source.LocalMeasuredExec control program heapLimit depth
      (.store (.bin .add base offset) stored)
      (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program)
        (.store (.bin .add base offset) stored)) target
      (target.setMem (arrayAddr (bufferRef placement buffer).base index) (cellWord w value)) := by
    rw [← address, ← storedValue]
    exact .store ⟨baseReads, offsetReads⟩ valueReads targetBound
  exact ⟨execution.erase, execution, represented.write written valueFits⟩

end Ram.LanguageCompiler.HeapRep
