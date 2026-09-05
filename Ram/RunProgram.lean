import Ram.Fast
import Ram.Named

/-!
# Compile once, run with a budget

Named programs use the same checked compiler and verified fast backend.
Preparation converts code to an array and computes a register preallocation
hint once; a prepared executable may be reused for many inputs.
-/

namespace Ram

structure Executable where
  code : Array Instr
  registerCapacity : Nat

def Executable.ofCode (code : Code) : Executable :=
  let instructions := code.toArray
  ⟨instructions, Fast.registerCapacity instructions⟩

def Executable.run (executable : Executable) (budget : Nat)
    (input : List (Word w)) : RunResult (Fast.State w) :=
  Fast.run executable.code budget (Fast.State.initial input executable.registerCapacity)

/-- Preparation and fast storage preserve the reference runner's entire result,
including the exact transition count, stopping reason, and all observations. -/
theorem Executable.run_eq (executable : Executable) (budget : Nat)
    (input : List (Word w)) :
    (executable.run budget input).map Fast.State.toState =
      Ram.run executable.code.toList budget (State.initial input) := by
  simpa only [Executable.run, Fast.State.toState_initial] using
    Fast.map_run executable.code budget (Fast.State.initial input executable.registerCapacity)

def Named.Bundle.executable (bundle : Named.Bundle) : Option Executable :=
  bundle.compile.map Executable.ofCode

end Ram
