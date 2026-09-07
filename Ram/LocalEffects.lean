/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Ram.Effects

/-!
# Registers outside the active local frame

The ABI reserves registers starting at `control`, while the current function
owns only registers below `locals`. Registers in between may hold an older
caller's values and must be preserved by the complete function execution.
-/

namespace Ram

def RegsPreservedAbove (control locals : Nat) (s t : State w) : Prop :=
  ∀ r, locals ≤ r → r < control → t.regs r = s.regs r

namespace RegsPreservedAbove

theorem refl (control locals : Nat) (s : State w) :
    RegsPreservedAbove control locals s s := fun _ _ _ => rfl

theorem trans {control locals : Nat} {s t u : State w}
    (hst : RegsPreservedAbove control locals s t)
    (htu : RegsPreservedAbove control locals t u) :
    RegsPreservedAbove control locals s u :=
  fun r hlo hhi => (htu r hlo hhi).trans (hst r hlo hhi)

theorem of_regs_eq {control locals : Nat} {s t : State w}
    (h : t.regs = s.regs) : RegsPreservedAbove control locals s t :=
  fun r _ _ => congrFun h r

theorem next (control locals : Nat) (s : State w) :
    RegsPreservedAbove control locals s s.next := of_regs_eq rfl

theorem atPC (control locals : Nat) (s : State w) (pc : Nat) :
    RegsPreservedAbove control locals s (s.atPC pc) := of_regs_eq rfl

theorem setReg {control locals : Nat} (s : State w) (dst : Reg) (value : Word w)
    (h : dst < locals) : RegsPreservedAbove control locals s (s.setReg dst value) := by
  intro r hlo _
  exact State.setReg_ne s dst r value
    (Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le h hlo)))

theorem setReg_above {control locals : Nat} (s : State w) (dst : Reg)
    (value : Word w) (h : control ≤ dst) :
    RegsPreservedAbove control locals s (s.setReg dst value) := by
  intro r _ hhi
  exact State.setReg_ne s dst r value
    (Nat.ne_of_lt (Nat.lt_of_lt_of_le hhi h))

theorem setMem (control locals : Nat) (s : State w) (address value : Word w) :
    RegsPreservedAbove control locals s (s.setMem address value) := of_regs_eq rfl

/-- Expression compilation writes only its scratch region. -/
theorem compile_expr (control locals : Nat) {e : Expr} {scratch : Reg} (s : State w)
    (hb : e.Bounded scratch) (hfresh : control ≤ scratch) :
    RegsPreservedAbove control locals s (execBlock (e.compile scratch) s) := by
  intro r _ hhi
  exact (Expr.compile_correct hb s).below r (Nat.lt_of_lt_of_le hhi hfresh)

end RegsPreservedAbove

namespace Source.State

/-- A source/target match can forget locals outside a smaller active frame. -/
theorem Matches.weaken {heapLimit k n : Nat} {s : Source.State w} {t : Ram.State w}
    (h : Matches heapLimit n s t) (hkn : k ≤ n) : Matches heapLimit k s t :=
  ⟨fun r hr => h.regs r (Nat.lt_of_lt_of_le hr hkn),
    h.heap, h.input, h.output, h.running⟩

end Source.State
end Ram
