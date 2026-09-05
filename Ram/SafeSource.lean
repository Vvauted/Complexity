import Ram.Memory

/-!
# Source executions confined to the heap and a bounded call depth

The additional index is an upper bound on simultaneously nested function
calls. It is not execution fuel or a time cost: sequencing and arbitrary
finite loops reuse the same depth budget. Each call needs one additional
level, and every source memory access stays below the heap boundary.

These are logical premises used to keep the compiler's private stack disjoint
from the source-visible heap. They do not introduce runtime bounds checks.
-/

namespace Ram.Source

/-- Successful source execution with heap-access and call-depth guarantees.
Pure local operations can run at depth zero. Calls consume one nesting level
only while the callee is active; sibling calls reuse that level. -/
inductive SafeExec (program : Program) (heapLimit : Nat) {w : Nat} :
    Nat → Stmt → State w → State w → Prop where
  | skip : SafeExec program heapLimit d .skip s s
  | assign (reads : value.ReadsBelow heapLimit s.regs s.mem) :
      SafeExec program heapLimit d (.assign dst value) s (s.setReg dst (s.eval value))
  | store (addressReads : address.ReadsBelow heapLimit s.regs s.mem)
      (valueReads : value.ReadsBelow heapLimit s.regs s.mem)
      (destination : (s.eval address).toNat < heapLimit) :
      SafeExec program heapLimit d (.store address value) s
        (s.setMem (s.eval address) (s.eval value))
  | seq (first : SafeExec program heapLimit d a s middle)
      (second : SafeExec program heapLimit d b middle t) :
      SafeExec program heapLimit d (.seq a b) s t
  | iteTrue (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c ≠ 0) (body : SafeExec program heapLimit d yes s t) :
      SafeExec program heapLimit d (.ite c yes no) s t
  | iteFalse (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c = 0) (body : SafeExec program heapLimit d no s t) :
      SafeExec program heapLimit d (.ite c yes no) s t
  | whileFalse (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c = 0) :
      SafeExec program heapLimit d (.while c body) s s
  | whileTrue (reads : c.ReadsBelow heapLimit s.regs s.mem)
      (condition : s.eval c ≠ 0) (body : SafeExec program heapLimit d b s middle)
      (rest : SafeExec program heapLimit d (.while c b) middle t) :
      SafeExec program heapLimit d (.while c b) s t
  | read (available : s.input = value :: rest) :
      SafeExec program heapLimit d (.read dst) s
        { s.setReg dst value with input := rest }
  | write (reads : value.ReadsBelow heapLimit s.regs s.mem) :
      SafeExec program heapLimit d (.write value) s
        { s with outputRev := s.eval value :: s.outputRev }
  | call (lookup : program[fn]? = some f) (arity : args.length = f.params)
      (frame : f.params ≤ f.locals)
      (arguments : ∀ arg ∈ args, arg.ReadsBelow heapLimit s.regs s.mem)
      (body : SafeExec program heapLimit d f.body (s.enter (args.map s.eval)) callee)
      (result : f.result.ReadsBelow heapLimit callee.regs callee.mem) :
      SafeExec program heapLimit (d + 1) (.call dst fn args) s
        (s.leave callee dst f.result)

namespace SafeExec

/-- The extra premises do not alter any successful source computation. -/
theorem erase {program : Program} {heapLimit depth : Nat}
    {stmt : Stmt} {s t : State w}
    (h : SafeExec program heapLimit depth stmt s t) : Exec program stmt s t := by
  induction h with
  | skip => exact .skip
  | assign _ => exact .assign
  | store _ _ _ => exact .store
  | seq _ _ first second => exact .seq first second
  | iteTrue _ condition _ body => exact .iteTrue condition body
  | iteFalse _ condition _ body => exact .iteFalse condition body
  | whileFalse _ condition => exact .whileFalse condition
  | whileTrue _ condition _ _ body rest => exact .whileTrue condition body rest
  | read available => exact .read available
  | write _ => exact .write
  | call lookup arity frame _ _ _ body => exact .call lookup arity frame body

/-- Unused call-depth capacity can be added without changing the execution. -/
theorem depth_add {program : Program} {heapLimit depth : Nat}
    {stmt : Stmt} {s t : State w}
    (h : SafeExec program heapLimit depth stmt s t) (extra : Nat) :
    SafeExec program heapLimit (depth + extra) stmt s t := by
  induction h with
  | skip => exact .skip
  | assign reads => exact .assign reads
  | store addressReads valueReads destination =>
      exact .store addressReads valueReads destination
  | seq _ _ first second => exact .seq first second
  | iteTrue reads condition _ body => exact .iteTrue reads condition body
  | iteFalse reads condition _ body => exact .iteFalse reads condition body
  | whileFalse reads condition => exact .whileFalse reads condition
  | whileTrue reads condition _ _ body rest =>
      exact .whileTrue reads condition body rest
  | read available => exact .read available
  | write reads => exact .write reads
  | call lookup arity frame arguments _ result body =>
      simpa only [Nat.add_right_comm _ 1 extra] using
        (SafeExec.call lookup arity frame arguments body result)

/-- The depth index is an upper bound, not a demand for exactly that depth. -/
theorem mono {program : Program} {heapLimit depth depth' : Nat}
    {stmt : Stmt} {s t : State w}
    (h : SafeExec program heapLimit depth stmt s t) (le : depth ≤ depth') :
    SafeExec program heapLimit depth' stmt s t := by
  have h' := h.depth_add (depth' - depth)
  simpa only [Nat.add_sub_of_le le] using h'

/-- Heap and depth bounds restrict admissible executions, never their result. -/
theorem deterministic {program : Program} {heapLimit heapLimit' depth depth' : Nat}
    {stmt : Stmt} {s t u : State w}
    (ht : SafeExec program heapLimit depth stmt s t)
    (hu : SafeExec program heapLimit' depth' stmt s u) : t = u :=
  ht.erase.deterministic hu.erase

end SafeExec

end Ram.Source
