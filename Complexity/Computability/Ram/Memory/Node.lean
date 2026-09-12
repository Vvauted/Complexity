/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Array.Contracts
import Complexity.Computability.Ram.Verification.Time.StraightLine

/-!
# Reading the three words of an immutable node

The block loads a node's head, option tag and tail address from their actual
memory cells. It changes only the three receiver registers and preserves the
whole memory and both streams. The final receiver may reuse the base register:
the address is consumed before that final assignment.

The endpoint is the three actual state updates, and the instruction count is
derived from the existing straight-line compiler theorem. Source identities,
typed payloads and valid tail links belong to the separate heap representation.
-/

namespace Ram.Source.Node

/-- The base survives until the last load. The three receivers are distinct,
but the final tail receiver may reuse the base register. -/
structure Registers where
  base : Reg
  head : Reg
  tag : Reg
  tail : Reg
  base_ne_head : base ≠ head
  base_ne_tag : base ≠ tag
  head_ne_tag : head ≠ tag
  head_ne_tail : head ≠ tail
  tag_ne_tail : tag ≠ tail

namespace Registers

/-- Load the three real node fields in their storage order. -/
def read (r : Registers) : Stmt :=
  .seq (.assign r.head (.load (.var r.base)))
    (.seq (.assign r.tag (.load (.bin .add (.var r.base) (.const 1))))
      (.assign r.tail (.load (.bin .add (.var r.base) (.const 2)))))

/-- The precise endpoint of the three loads, with the entry base retained until
its last use. No mathematical decoding or additional execution is performed. -/
def loaded (r : Registers) (entry : State w) : State w :=
  ((entry.setReg r.head (entry.mem (entry.regs r.base))).setReg r.tag
    (entry.mem (arrayAddr (entry.regs r.base) 1))).setReg r.tail
      (entry.mem (arrayAddr (entry.regs r.base) 2))

/-- Node reading has no branch, loop or function call. -/
theorem read_isStraightLine (r : Registers) : r.read.IsStraightLine := by
  simp [read, Stmt.IsStraightLine]

/-- The complete node interval is represented at the actual base operand. -/
structure Pre (r : Registers) (heapLimit : Nat)
    (base headValue tagValue tailValue : Word w) (entry : State w) : Prop where
  array : ArrayAt heapLimit base [headValue, tagValue, tailValue] entry
  base_reg : entry.regs r.base = base

/-- The three words are received unchanged, with all memory, other registers
and both streams retained. No validity of a source-level tail is assumed here. -/
structure Post (r : Registers) (heapLimit : Nat)
    (base headValue tagValue tailValue : Word w) (entry finish : State w) : Prop where
  head_reg : finish.regs r.head = headValue
  tag_reg : finish.regs r.tag = tagValue
  tail_reg : finish.regs r.tail = tailValue
  memory : finish.mem = entry.mem
  other : ∀ slot, slot ≠ r.head → slot ≠ r.tag → slot ≠ r.tail →
    finish.regs slot = entry.regs slot
  input : finish.input = entry.input
  output : finish.outputRev = entry.outputRev

/-- Each actual load lies inside the represented three-word interval. -/
theorem read_safe (r : Registers) {program : Program} {heapLimit depth : Nat}
    {base headValue tagValue tailValue : Word w} {entry : State w}
    (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    SafeExec program heapLimit depth r.read entry (r.loaded entry) := by
  have addressBelow (index : Nat) (bound : index < 3) :
      (arrayAddr base index).toNat < heapLimit :=
    pre.array.addr_lt (by simpa using bound)
  have execution := SafeExec.seq
    (SafeExec.assign (program := program) (heapLimit := heapLimit) (d := depth)
      (s := entry) (dst := r.head) (value := .load (.var r.base))
      ⟨trivial, by
        simpa [State.eval, Expr.eval, pre.base_reg, arrayAddr]
          using addressBelow 0 (by decide)⟩)
    (SafeExec.seq
      (SafeExec.assign (dst := r.tag)
        (value := .load (.bin .add (.var r.base) (.const 1)))
        ⟨⟨trivial, trivial⟩, by
          simpa [State.eval, Expr.eval, BinOp.eval, State.setReg,
            pre.base_reg, r.base_ne_head, arrayAddr]
            using addressBelow 1 (by decide)⟩)
      (SafeExec.assign (dst := r.tail)
        (value := .load (.bin .add (.var r.base) (.const 2)))
        ⟨⟨trivial, trivial⟩, by
          simpa [State.eval, Expr.eval, BinOp.eval, State.setReg,
            pre.base_reg, r.base_ne_head, r.base_ne_tag, arrayAddr]
            using addressBelow 2 (by decide)⟩))
  simpa [read, loaded, State.eval, Expr.eval, BinOp.eval, State.setReg,
    arrayAddr, r.base_ne_head, r.base_ne_tag] using execution

/-- The exact endpoint exposes the original node words without changing its
storage or any other heap object. -/
theorem loaded_post (r : Registers) {heapLimit : Nat}
    {base headValue tagValue tailValue : Word w} {entry : State w}
    (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    r.Post heapLimit base headValue tagValue tailValue entry (r.loaded entry) := by
  have headRead : entry.mem base = headValue := by
    simpa [arrayAddr] using pre.array.1.lookup 0 (by simp)
  have tagRead : entry.mem (arrayAddr base 1) = tagValue := by
    simpa using pre.array.1.lookup 1 (by simp)
  have tailRead : entry.mem (arrayAddr base 2) = tailValue := by
    simpa using pre.array.1.lookup 2 (by simp)
  refine ⟨?_, ?_, ?_, rfl, ?_, rfl, rfl⟩
  · simp [loaded, State.setReg, r.head_ne_tag, r.head_ne_tail, pre.base_reg, headRead]
  · simp [loaded, State.setReg, r.tag_ne_tail, pre.base_reg, tagRead]
  · simp [loaded, State.setReg, pre.base_reg, tailRead]
  · intro slot differentHead differentTag differentTail
    simp [loaded, State.setReg, differentHead, differentTag, differentTail]

/-- The existing compiler emits thirteen instructions for these three loads. -/
theorem read_stmtSize (r : Registers) (control : Nat) (localsTable : Nat → Nat) :
    LocalCompiler.stmtSize control localsTable r.read = 13 := rfl

/-- The same safe execution has the exact compiler-derived count and retains
the full register and memory postcondition at its actual endpoint. -/
theorem read_measured (r : Registers) {program : Program}
    {control heapLimit depth : Nat} {base headValue tagValue tailValue : Word w}
    {entry : State w} (pre : r.Pre heapLimit base headValue tagValue tailValue entry) :
    LocalMeasuredExec control program heapLimit depth r.read
        (LocalCompiler.stmtSize control (LocalCompiler.calleeLocals program) r.read)
        entry (r.loaded entry) ∧
      r.Post heapLimit base headValue tagValue tailValue entry (r.loaded entry) := by
  obtain ⟨steps, execution⟩ :=
    (r.read_safe (program := program) (depth := depth) pre).exists_localMeasured control
  have count := execution.steps_eq_stmtSize r.read_isStraightLine
  refine ⟨?_, r.loaded_post pre⟩
  simpa only [count] using execution

end Registers
end Ram.Source.Node
