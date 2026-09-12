/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Basic
import Complexity.Language.Syntax.Native
import Lean.Elab.Command
import Lean.EnvExtension

/-!
# Source program headers for frontend imports

The named frontend records public function headers after elaborating their
source program. Lean's persistent environment extension carries these headers
across module imports. The key is the resolved `family.program` declaration,
so ordinary namespace and open-name resolution determine the imported family.
Structured headers retain the core's recursive product and option types,
including borrowed buffers inside them; they require no separate import encoding.

This metadata routes named calls; it contains no implementation, execution
assumption or cost annotation. Actual source bodies and their embedding proofs
remain declarations checked by Lean. The headers do not enumerate every entry
of an extended program's table: imported bodies can occupy other entries.
-/

namespace Complexity.Language.Syntax

open Lean Lean.Elab.Command

/-- A named source function's public header, without its implementation.
`name` is its local declaration name within the source family; parameter names
are retained for generated ordinary-argument proof interfaces. -/
structure FunctionInfo where
  name : Name
  params : Array (Name × Ty)
  result : Ty
  /-- The public value function has a checked pure source correspondence.
  Its actual source observation has the explicit `_action` suffix. -/
  pure : Bool := false
  /-- The independently checked native header, when a represented pure family
  uses registered structures rather than the core's native value types. -/
  nativeHeader : Option NativeHeader := none

private initialize programInfoExt :
    SimplePersistentEnvExtension (Name × Array FunctionInfo) (NameMap (Array FunctionInfo)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state entry => state.insert entry.1 entry.2
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
  }

private def resolveProgramName (family : TSyntax `ident) : CommandElabM Name :=
  resolveGlobalConstNoOverload (mkIdentFrom family (family.getId ++ `program))

/-- Record the public local headers of an already elaborated source program.
The frontend calls this after elaborating all generated declarations. -/
def registerProgramInfo (family : TSyntax `ident) (functions : Array FunctionInfo) :
    CommandElabM Unit := do
  let programName ← resolveProgramName family
  modifyEnv fun env => programInfoExt.addEntry env (programName, functions)

/-- Resolve a named source program and recover its actual full family name and
public local headers. An arbitrary Lean declaration is not a source import. -/
def getProgramInfo (family : TSyntax `ident) : CommandElabM (Name × Array FunctionInfo) := do
  let programName ← resolveProgramName family
  let some functions := (programInfoExt.getState (← getEnv)).find? programName
    | throwErrorAt family "'{family.getId}' is not a registered source program"
  return (programName.getPrefix, functions)

end Complexity.Language.Syntax
