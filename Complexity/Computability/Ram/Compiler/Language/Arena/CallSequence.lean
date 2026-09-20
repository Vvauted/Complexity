/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Arena.Realization

/-!
# Arena readiness across standalone calls

A standalone call discards its result, restores caller locals and keeps the
callee's actual final heap. The following rule composes resource certificates
for the callee and the next statement along the given source execution.
The continuation can use that same callee execution to obtain its source
postcondition; no independent execution or termination proof is required.
-/

namespace Ram.LanguageCompiler.ArenaReady

open Complexity.Language

/-- Compose readiness for a standalone call and its continuation. The callee
uses one fewer stack level; the continuation starts at its actual final heap
and arena cursor, with the caller's locals restored. The three arena cursors
need not coincide. -/
theorem call_seq_of_exec {signatures : List Signature}
    {program : Complexity.Language.Program signatures}
    {w heapLimit depth cursor calleeCursor finalCursor : Nat}
    {Γ : List Ty} {result : Ty} {entry finish : Complexity.Language.State Γ}
    {control : Control result} {fn : Fin signatures.length}
    {args : Args Γ signatures[fn].params}
    {second : Complexity.Language.Stmt signatures Γ result}
    (arguments : EnvFits w (args.eval entry.locals))
    (calleeReady : ∀ calleeFinish value
      (callee : Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value)),
      ArenaReady callee w heapLimit depth cursor calleeCursor)
    (tailReady : ∀ calleeFinish value
      (callee : Complexity.Language.Exec program (program.body fn)
        (entry.enter (args.eval entry.locals)) calleeFinish (.returned value))
      (tail : Complexity.Language.Exec program second
        (entry.restore calleeFinish) finish control),
      ArenaReady tail w heapLimit (depth + 1) calleeCursor finalCursor)
    (execution : Complexity.Language.Exec program
      (.seq (.call fn args .skip) second) entry finish control)
    (successful : ControlFits w control) :
    ArenaReady execution w heapLimit (depth + 1) cursor finalCursor := by
  cases execution with
  | seqNormal called continued =>
      have actualCall := called
      cases called with
      | callReturn callee body =>
          cases body with
          | skip =>
              exact .seqNormal (head := actualCall)
                (.callReturn arguments (calleeReady _ _ callee) (.skip _))
                (tailReady _ _ callee continued)
  | seqReturn called =>
      cases called with
      | callReturn callee body => cases body
  | seqFault called => exact False.elim successful

end Ram.LanguageCompiler.ArenaReady
