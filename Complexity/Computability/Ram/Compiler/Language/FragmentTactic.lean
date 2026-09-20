/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Computability.Ram.Compiler.Language.Arena.CallSequence
import Complexity.Computability.Ram.Compiler.Language.Tactic

/-!
# Resource proofs for named loop fragments

`ram_source_fragment_realize` selects the registered coordinates of the actual
named guard or body, then uses the existing structural realization pass. The
entry's private completion slots and visible locals are normalized together;
their ranges remain ordinary mathematical obligations.

`ram_source_fragment_arena_call using calleeReady` handles a standalone call
followed by a fixed-placement continuation in the named fragment. It reuses the
supplied readiness of each actual callee execution, checks its real arguments,
and realizes the continuation at that callee's actual final heap. Caller-local
restoration and execution cases are handled by the shared call-sequence rule.
The continuation retains the callee's cursor; no reset or effect-free callee is
assumed. Allocating continuations can use that shared rule directly instead.

Neither entry unfolds a callee implementation, infers a resource invariant, or
adds an instruction budget or a second termination proof.
-/

namespace Ram.LanguageCompiler.FragmentTactic

open Lean Meta Elab Tactic

/-- Select coordinates by the actual named fragment, not by its environment's
shape. The registered entry initializes completion slots in the same source. -/
private def normalize (head : Name) (position : Nat) : TacticM Unit := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData.headBeta.consumeMData
  unless target.isAppOf head do
    throwError "expected a {head} goal for a named source loop fragment"
  let some statement := target.getAppArgs[position]? |
    throwError "expected a complete {head} goal for a named source loop fragment"
  let .const fragment _ := statement.consumeMData.getAppFn |
    throwError "the goal must retain a named source loop's Guard or Body declaration"
  let site := fragment.getPrefix
  unless fragment == site ++ `Guard || fragment == site ++ `Body do
    throwError "the goal must retain a named source loop's Guard or Body declaration"
  let some coordinates := Complexity.Language.Syntax.getLoopCoordinates? (← getEnv) (site ++ `Code) |
    throwError "the named source fragment has no registered loop coordinates"
  let rules := coordinates.rules ++
    coordinates.completion?.toArray.map (·.entry)
  Ram.LanguageCompiler.Tactic.normalizeSourceCoordinates rules
    (some (← `(Lean.Parser.Tactic.location| at *)))

private def realize : TacticM Unit := do
  normalize ``RealizationWP 6
  evalTactic (← `(tactic| ram_source_realize_step))

private def arenaCall (callee : TSyntax `term) : TacticM Unit := do
  normalize ``ArenaReady 4
  evalTactic (← `(tactic|
    apply ArenaReady.call_seq_of_exec (calleeReady := $callee)
      (successful := by assumption)))
  evalTactic (← `(tactic|
    all_goals first
    | case' tailReady =>
        intro calleeFinish value invoked tail
        apply RealizationWP.arenaReady
          (normal := fun _ => True) (returned := fun _ _ => True) (execution := tail)
        ram_source_realize_step
    | skip))
  Ram.LanguageCompiler.Tactic.onGoals do
    Ram.LanguageCompiler.Tactic.normalizeValues
    unless (← getGoals).isEmpty do
      evalTactic (← `(tactic| (repeat' apply And.intro) <;> try assumption))

/-- Realize the actual named guard or body using its checked source coordinates
and the existing structural rules. Word ranges and unsupported calls remain
explicit obligations; no callee body or loop is unfolded. -/
syntax (name := sourceFragmentRealize) "ram_source_fragment_realize" : tactic

elab_rules : tactic
  | `(tactic| ram_source_fragment_realize) => realize

/-- Compose supplied actual callee readiness with the named fragment's
fixed-placement continuation. The same heap, independent cursors and call depth
are retained; scalar ranges remain ordinary proof goals. -/
syntax (name := sourceFragmentArenaCall)
  "ram_source_fragment_arena_call" " using " term : tactic

elab_rules : tactic
  | `(tactic| ram_source_fragment_arena_call using $callee) => arenaCall callee

end Ram.LanguageCompiler.FragmentTactic
