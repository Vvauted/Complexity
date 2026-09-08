/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Expr.Basic

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

/-- The first return field uses the scalar return register. Further fields
reuse the protected argument buffer after the callee has finished its body. -/
def resultReg (n : Nat) : Nat → Reg
  | 0 => rv n
  | i + 1 => arg n i

@[simp] theorem resultReg_zero (n : Nat) : resultReg n 0 = rv n := rfl

@[simp] theorem resultReg_succ (n i : Nat) : resultReg n (i + 1) = arg n i := rfl

/-- Return fields are outside every source local register. -/
theorem lt_resultReg (n i : Nat) : n < resultReg n i := by
  cases i <;> simp [resultReg, rv, arg] <;> omega

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

/-- Evaluate each return field in the callee frame before restoring its caller.
The tail uses the same individually evaluated buffer as function arguments. -/
def evalResults (n : Nat) : List Expr → Code
  | [] => []
  | e :: es =>
      e.compile (scratch n) ++ .move (rv n) (scratch n) :: evalArgs n 0 es

/-- Receive return fields with actual moves, in destination order. Repeated
destinations have ordinary last-write-wins behavior; no bulk assignment is implicit. -/
def receiveResults (n : Nat) : Nat → List Reg → Code
  | _, [] => []
  | i, dst :: dsts => .move dst (resultReg n i) :: receiveResults n (i + 1) dsts

@[simp] theorem evalResults_nil (n : Nat) : evalResults n [] = [] := rfl

@[simp] theorem evalResults_singleton (n : Nat) (result : Expr) :
    evalResults n [result] =
      result.compile (scratch n) ++ [.move (rv n) (scratch n)] := rfl

@[simp] theorem receiveResults_nil (n start : Nat) : receiveResults n start [] = [] := rfl

@[simp] theorem receiveResults_singleton (n start dst : Nat) :
    receiveResults n start [dst] = [.move dst (resultReg n start)] := rfl

@[simp] theorem receiveResults_length (n start : Nat) (dsts : List Reg) :
    (receiveResults n start dsts).length = dsts.length := by
  induction dsts generalizing start with
  | nil => rfl
  | cons dst dsts ih => simp [receiveResults, ih]

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

/-- A call receives each returned field after its entry jump. With no fields,
the saved return address points directly to the caller's continuation. -/
def callCodeResults (n entry : Nat) (dsts : List Reg) (args : List Expr) (base : Nat) : Code :=
  let returnPC := base + (callPrefix n args 0).length + 1
  callPrefix n args returnPC ++ .jump entry :: receiveResults n 0 dsts

/-- Buffer all return expressions before restoring the caller's local frame. -/
def returnPrefixResults (n : Nat) (results : List Expr) : Code :=
  evalResults n results ++ retreat n ++
    [.load (ra n) (sp n)] ++ restoreLocals n n

/-- Return the buffered fields by jumping to the saved caller continuation. -/
def returnCodeResults (n : Nat) (results : List Expr) : Code :=
  returnPrefixResults n results ++ [.jumpReg (ra n)]

def callCode (n entry dst : Nat) (args : List Expr) (base : Nat) : Code :=
  callCodeResults n entry [dst] args base

def returnPrefix (n : Nat) (result : Expr) : Code :=
  returnPrefixResults n [result]

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

theorem callCodeResults_length (n entry : Nat) (dsts : List Reg)
    (args : List Expr) (base : Nat) :
    (callCodeResults n entry dsts args base).length =
      (callPrefix n args 0).length + (dsts.length + 1) := by
  simp only [callCodeResults, List.length_append, List.length_cons, receiveResults_length]
  rw [callPrefix_length n args _ 0]

theorem callCode_length (n entry dst : Nat) (args : List Expr) (base : Nat) :
    (callCode n entry dst args base).length = (callPrefix n args 0).length + 2 :=
  callCodeResults_length n entry [dst] args base

end Ram.ABI
