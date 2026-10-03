/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePrepared
import Complexity.Computability.Ram.Compiler.Language.Buffer.PrepareSpace
import Complexity.Computability.Ram.Compiler.Language.List.PrepareSpace

/-!
# Concrete loader connections for prepared session footprints

The existing Buffer and List loaders supply actual invocation-based preparation
footprints, including allocation, initialization, writes and wrapper accesses.
These specializations connect them directly to the generic prepared session
relations. The source projection retains the real intermediate heap. Neither
loader is a free mathematical conversion, and neither relation is candidate-
selected. External transport remains outside the numerical preparation boundary.
-/

namespace Ram.LanguageCompiler.Session

open Complexity.Language
variable {configuration : List Ty} {response : Ty} {w heapLimit : Nat}

/-- Concrete current-array preparation erases to the original counted loader
and the same callbacks, without resetting either memory or instruction count. -/
theorem PreparedSpaceRuns.buffer_erase
    {session : Complexity.Language.Session configuration [.buffer .nat] response}
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Array Nat)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session Buffer.Prepare.prepareSpace args current inputs replies
      finish finalMemory steps seed footprint) :
    PreparedRuns session Buffer.Prepare.prepare args current inputs replies finish finalMemory
      steps :=
  run.erase (fun _ _ _ _ _ _ _ loaded => Buffer.Prepare.prepareSpace_erase loaded)

/-- Concrete Buffer preparation projects its actual allocated and written data
to the source callback history; private state is never reconstructed. -/
theorem PreparedSpaceRuns.buffer_source
    {session : Complexity.Language.Session configuration [.buffer .nat] response}
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (Array Nat)} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session Buffer.Prepare.prepareSpace args current inputs replies
      finish finalMemory steps seed footprint) :
    session.PreparedRuns
      (fun values heap arguments finalHeap =>
        Complexity.Language.Buffer.Prepare.Run values heap arguments.head finalHeap)
      args current.heap inputs replies finish finalMemory.heap :=
  run.source (fun _ _ _ _ _ _ _ loaded => Buffer.Prepare.prepareSpace_source loaded)

/-- Concrete list preparation retains the fixed shared tail and all actual
constructor invocations in the original counted session history. -/
theorem PreparedSpaceRuns.list_erase (kind : CellTy) (tail : Option (NodeRef kind))
    {session : Complexity.Language.Session configuration [.option (.node kind)] response}
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (List (CellValue kind))} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session (List.Prepare.prepareSpace kind tail) args current inputs
      replies finish finalMemory steps seed footprint) :
    PreparedRuns session (List.Prepare.prepare kind tail) args current inputs replies finish
      finalMemory steps :=
  run.erase (fun _ _ _ _ _ _ _ loaded => List.Prepare.prepareSpace_erase loaded)

/-- The original heap-backed list source loader, with its shared suffix, feeds
the same callbacks and actual retained memory. -/
theorem PreparedSpaceRuns.list_source (kind : CellTy) (tail : Option (NodeRef kind))
    {session : Complexity.Language.Session configuration [.option (.node kind)] response}
    {args : Env configuration} {current finalMemory : State w heapLimit}
    {inputs : List (List (CellValue kind))} {replies : List (Value response × Heap)}
    {finish : Value session.stateTy} {steps : Nat} {seed footprint : Finset (Word w)}
    (run : PreparedSpaceRuns session (List.Prepare.prepareSpace kind tail) args current inputs
      replies finish finalMemory steps seed footprint) :
    session.PreparedRuns
      (fun values heap arguments finalHeap =>
        Complexity.Language.List.Prepare.Run kind values tail heap arguments.head finalHeap)
      args current.heap inputs replies finish finalMemory.heap :=
  run.source (fun _ _ _ _ _ _ _ loaded => List.Prepare.prepareSpace_source loaded)

end Ram.LanguageCompiler.Session
