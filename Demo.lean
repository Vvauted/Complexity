import Ram.RunProgram

/-!
A runnable example and small wall-clock measurement driver, not a test suite.
The program writes an array of consecutive words and then sums it. Both
backends execute identical compiled code and input under the same step budget.
Elapsed time covers execution, not source compilation or executable preparation.
-/

open Ram Ram.DSL

def arraySumProgram : Named.Bundle := ram_program% {
  main locals (size, i, total) {
    read size;
    i := 0;
    total := 0;
    while i < size {
      store[i] := i;
      i += 1;
    }
    i := 0;
    while i < size {
      total += load[i];
      i += 1;
    }
    write total;
  }
}

-- Keep the pure interpreter call inside the measured IO interval. Without an
-- opaque call boundary the compiler may move pure evaluation past the clock.
@[noinline] def executeFast (executable : Executable) (budget : Nat)
    (input : List (Word 64)) : IO (RunResult (Fast.State 64)) :=
  pure (executable.run budget input)

@[noinline] def executeReference (code : Code) (budget : Nat)
    (input : List (Word 64)) : IO (RunResult (State 64)) :=
  pure (Ram.run code budget (State.initial input))

def main (args : List String) : IO UInt32 := do
  let backend := args[0]?.getD "fast"
  let size := (args[1]?.bind String.toNat?).getD 10000
  if backend != "fast" && backend != "reference" then
    IO.eprintln "usage: lake exe ram-demo [fast|reference] [array-length]"
    return 1
  let some executable := arraySumProgram.executable
    | IO.eprintln "RAM source did not compile"; return 1
  -- The first word is the compiler's heap/stack boundary, the second is input.
  let input : List (Word 64) := [BitVec.ofNat 64 size, BitVec.ofNat 64 size]
  let budget := 50 * size + 100
  if backend == "fast" then
    let start ← IO.monoNanosNow
    let result ← executeFast executable budget input
    let elapsed := (← IO.monoNanosNow) - start
    IO.println s!"backend={backend} size={size} steps={result.steps} reason={repr result.reason} output={result.state.output.map BitVec.toNat} elapsed_ns={elapsed}"
    return if result.reason == .halted then 0 else 2
  else
    let code := executable.code.toList
    let start ← IO.monoNanosNow
    let result ← executeReference code budget input
    let elapsed := (← IO.monoNanosNow) - start
    IO.println s!"backend={backend} size={size} steps={result.steps} reason={repr result.reason} output={result.state.output.map BitVec.toNat} elapsed_ns={elapsed}"
    return if result.reason == .halted then 0 else 2
