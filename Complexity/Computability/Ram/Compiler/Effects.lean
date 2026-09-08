/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.ABI.Basic
import Complexity.Computability.Ram.Compiler.ABI.Frame.Basic
import Complexity.Computability.Ram.Compiler.Control
import Complexity.Computability.Ram.Memory.Basic

/-!
# Source-visible effects and preservation of older stack frames

A compiled statement keeps its entry stack pointer and every already occupied
stack word. It may change the heap and use words above the entry stack pointer.
This small frame relation composes without assuming that the whole heap and
stack are identical in source and target states.
-/

namespace Ram

structure FramePreserved (n heapLimit : Nat) (s t : State w) : Prop where
  sp : t.regs (ABI.sp n) = s.regs (ABI.sp n)
  older : ∀ a, heapLimit ≤ a.toNat → a.toNat < (s.regs (ABI.sp n)).toNat →
    t.mem a = s.mem a

namespace FramePreserved

theorem refl (n heapLimit : Nat) (s : State w) : FramePreserved n heapLimit s s :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem trans {n heapLimit : Nat} {s t u : State w}
    (hst : FramePreserved n heapLimit s t) (htu : FramePreserved n heapLimit t u) :
    FramePreserved n heapLimit s u := by
  refine ⟨htu.sp.trans hst.sp, ?_⟩
  intro a ha hb
  have hb' : a.toNat < (t.regs (ABI.sp n)).toNat := by rw [hst.sp]; exact hb
  exact (htu.older a ha hb').trans (hst.older a ha hb)

/-- A saved frame inside the protected older-stack interval survives between
the endpoints. Its upper bound supplies non-wrapping slot addresses; the heap
and newer stack need not be unchanged. This does not assert absence of writes. -/
theorem frameSaved {control heapLimit locals : Nat} {start finish : State w}
    {base : Word w} {savedRegs : Reg → Word w}
    (frame : FramePreserved control heapLimit start finish)
    (lower : heapLimit ≤ base.toNat)
    (upper : base.toNat + ABI.frameSize locals ≤ (start.regs (ABI.sp control)).toNat)
    (saved : ABI.FrameSaved locals base savedRegs start.mem) :
    ABI.FrameSaved locals base savedRegs finish.mem := by
  apply saved.congr
  intro i hi
  have slotUpper : base.toNat + (i + 1) < (start.regs (ABI.sp control)).toNat := by
    simp only [ABI.frameSize] at upper
    omega
  have slotAddress := arrayAddr_toNat (Nat.lt_trans slotUpper (BitVec.isLt _))
  apply frame.older
  · rw [slotAddress]
    omega
  · rw [slotAddress]
    exact slotUpper

theorem of_eq {n heapLimit : Nat} {s t : State w}
    (hr : t.regs (ABI.sp n) = s.regs (ABI.sp n)) (hm : t.mem = s.mem) :
    FramePreserved n heapLimit s t := ⟨hr, fun a _ _ => congrFun hm a⟩

theorem next (n heapLimit : Nat) (s : State w) : FramePreserved n heapLimit s s.next :=
  of_eq rfl rfl

theorem atPC (n heapLimit : Nat) (s : State w) (pc : Nat) :
    FramePreserved n heapLimit s (s.atPC pc) := of_eq rfl rfl

theorem setReg {n heapLimit : Nat} (s : State w) (dst : Reg) (value : Word w)
    (h : ABI.sp n ≠ dst) : FramePreserved n heapLimit s (s.setReg dst value) :=
  of_eq (State.setReg_ne s dst (ABI.sp n) value h) rfl

/-- An actual source-heap store cannot change any older compiler stack word. -/
theorem setMem {n heapLimit : Nat} (s : State w) (address value : Word w)
    (ha : address.toNat < heapLimit) :
    FramePreserved n heapLimit s (s.setMem address value) := by
  refine ⟨rfl, ?_⟩
  intro a hlow _
  apply State.setMem_ne
  intro heq
  subst a
  omega

theorem compile_expr (n heapLimit : Nat) {e : Expr} {r : Reg} (s : State w)
    (hb : e.Bounded r) (hsp : ABI.sp n < r) :
    FramePreserved n heapLimit s (execBlock (e.compile r) s) :=
  of_eq ((Expr.compile_correct hb s).below _ hsp) (Expr.compile_correct hb s).memory

end FramePreserved

namespace Source.State

theorem Matches.next {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) : Matches heapLimit locals s t.next :=
  ⟨h.regs, h.heap, h.input, h.output, h.running⟩

theorem Matches.atPC {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) (pc : Nat) :
    Matches heapLimit locals s (t.atPC pc) :=
  ⟨h.regs, h.heap, h.input, h.output, h.running⟩

theorem Matches.setReg {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) (dst : Reg) (value : Word w) :
    Matches heapLimit locals (s.setReg dst value) (t.setReg dst value) := by
  refine ⟨?_, h.heap, h.input, h.output, h.running⟩
  intro r hr
  by_cases heq : r = dst
  · subst r
    simp
  · simp only [Source.State.setReg_ne _ _ _ _ heq, Ram.State.setReg_ne _ _ _ _ heq]
    exact h.regs r hr

theorem Matches.setMem {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) (address value : Word w) :
    Matches heapLimit locals (s.setMem address value) (t.setMem address value) := by
  refine ⟨h.regs, ?_, h.input, h.output, h.running⟩
  intro a ha
  by_cases heq : a = address
  · subst a
    simp
  · simp only [Source.State.setMem_ne _ _ _ _ heq, Ram.State.setMem_ne _ _ _ _ heq]
    exact h.heap a ha

theorem Matches.write {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) (src : Reg) (value : Word w)
    (hv : t.regs src = value) :
    Matches heapLimit locals { s with outputRev := value :: s.outputRev }
      (execInstr (.write src) t) := by
  refine ⟨h.regs, h.heap, h.input, ?_, h.running⟩
  simp only [execInstr, Ram.State.next_regs, hv, h.output]

theorem Matches.read {heapLimit locals : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit locals s t) (dst : Reg) (value : Word w) (rest : List (Word w))
    (hi : s.input = value :: rest) :
    Matches heapLimit locals { s.setReg dst value with input := rest }
      (execInstr (.read dst) t) := by
  have hit : t.input = value :: rest := h.input.symm.trans hi
  have hu := h.setReg dst value
  simp only [execInstr, hit]
  exact ⟨hu.regs, hu.heap, rfl, hu.output, hu.running⟩

end Source.State
end Ram
