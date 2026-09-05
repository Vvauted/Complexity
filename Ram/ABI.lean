import Ram.ExprCompile

/-!
# Concrete calling-convention code

All frames are finite sequences of ordinary RAM loads and stores. The complete
program fixes `n`, the common local-register bound, before any input is supplied.
These definitions emit code; their lengths are not a second execution-cost
semantics. The simulation proofs connect them to `Ram.Exec`.
-/

namespace Ram.ABI

def sp (n : Nat) : Reg := n
def rv (n : Nat) : Reg := n + 1
def ra (n : Nat) : Reg := n + 2
def addr (n : Nat) : Reg := n + 3
def tmp (n : Nat) : Reg := n + 4
def arg (n i : Nat) : Reg := n + 5 + i
def scratch (n : Nat) : Reg := 2 * n + 5
def frameSize (n : Nat) : Nat := n + 1

/-- Compute a stack slot from the current SP. -/
def slotAddress (n i : Nat) : Code :=
  [.const (tmp n) (i + 1), .binop .add (addr n) (sp n) (tmp n)]

def saveLocal (n i : Nat) : Code := slotAddress n i ++ [.store (addr n) i]
def restoreLocal (n i : Nat) : Code := slotAddress n i ++ [.load i (addr n)]

/-- Emitting `k` individual stores, in ascending register order. -/
def saveLocals (n : Nat) : Nat → Code
  | 0 => []
  | k + 1 => saveLocals n k ++ saveLocal n k

/-- Emitting `k` individual loads, in ascending register order. -/
def restoreLocals (n : Nat) : Nat → Code
  | 0 => []
  | k + 1 => restoreLocals n k ++ restoreLocal n k

def saveReturn (n returnPC : Nat) : Code :=
  [.const (tmp n) returnPC, .store (sp n) (tmp n)]

/-- Pure source arguments are evaluated before any source local is overwritten. -/
def evalArgs (n : Nat) : Nat → List Expr → Code
  | _, [] => []
  | i, e :: es =>
      e.compile (scratch n) ++ [.move (arg n i) (scratch n)] ++ evalArgs n (i + 1) es

/-- Initialize locals from the protected argument buffer, zeroing nonparameters. -/
def initLocal (n params i : Nat) : Instr :=
  if i < params then .move i (arg n i) else .const i 0

def initLocals (n params : Nat) : Nat → Code
  | 0 => []
  | k + 1 => initLocals n params k ++ [initLocal n params k]

def advance (n : Nat) : Code :=
  [.const (tmp n) (frameSize n), .binop .add (sp n) (sp n) (tmp n)]

def retreat (n : Nat) : Code :=
  [.const (tmp n) (frameSize n), .binop .sub (sp n) (sp n) (tmp n)]

def callPrefix (n : Nat) (args : List Expr) (returnPC : Nat) : Code :=
  evalArgs n 0 args ++ saveReturn n returnPC ++ saveLocals n n ++
    initLocals n args.length n ++ advance n

/-- The return label is the receive instruction immediately after the call
jump. Label values do not change the prefix length. -/
def callCode (n entry dst : Nat) (args : List Expr) (base : Nat) : Code :=
  let returnPC := base + (callPrefix n args 0).length + 1
  callPrefix n args returnPC ++ [.jump entry, .move dst (rv n)]

/-- Evaluate the result in the callee frame, then restore the caller frame. -/
def returnPrefix (n : Nat) (result : Expr) : Code :=
  result.compile (scratch n) ++ [.move (rv n) (scratch n)] ++ retreat n ++
    [.load (ra n) (sp n)] ++ restoreLocals n n

def returnCode (n : Nat) (result : Expr) : Code :=
  returnPrefix n result ++ [.jumpReg (ra n)]

@[simp] theorem saveLocal_length (n i : Nat) : (saveLocal n i).length = 3 := rfl
@[simp] theorem restoreLocal_length (n i : Nat) : (restoreLocal n i).length = 3 := rfl

@[simp] theorem saveLocals_length (n k : Nat) : (saveLocals n k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [saveLocals, ih, Nat.mul_add]

@[simp] theorem restoreLocals_length (n k : Nat) : (restoreLocals n k).length = 3 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [restoreLocals, ih, Nat.mul_add]

@[simp] theorem initLocals_length (n params k : Nat) : (initLocals n params k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [initLocals, ih]

theorem callPrefix_length (n : Nat) (args : List Expr) (a b : Nat) :
    (callPrefix n args a).length = (callPrefix n args b).length := by
  simp [callPrefix, saveReturn]

theorem callCode_length (n entry dst : Nat) (args : List Expr) (base : Nat) :
    (callCode n entry dst args base).length = (callPrefix n args 0).length + 2 := by
  simp only [callCode, List.length_append, List.length_cons, List.length_nil]
  rw [callPrefix_length n args _ 0]

end Ram.ABI
