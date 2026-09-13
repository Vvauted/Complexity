/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Program.Deriving
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayInput

/-!
# Deriving a fixed RAM input for an ordinary record

After deriving `Complexity.Program.Input`, a record can also derive
`Complexity.Program.RamInput`. The handler reuses the same checked direct-field
embedding and existing field layout, including its actual memory, cursor,
word-width scale and initialization proofs. It neither changes the source
program nor chooses capacity or a proposed runtime bound.

The derived source input must be definitionally the direct-field presentation.
An independently chosen manual input layout needs its own physical connection,
not an automatic cast to a different layout.
-/

namespace Complexity.Program.Deriving

open Lean Meta Elab Command

private def deriveRamInput (name : Name) : TermElabM Unit := do
  let embedding ← ensureStructureEmbedding name
  let value ← mkAppM ``RamInput.comap #[embedding]
  let expected ← mkAppOptM ``RamInput #[some (mkConst name), none]
  unless ← isDefEq (← inferType value) expected do
    throwError "RamInput deriving requires the same direct-field Input instance; \
      derive Complexity.Program.Input first"
  addInterfaceInstance (name ++ `instProgramRamInput) value
    "The fixed RAM layout of this record's derived mathematical program input."

private def ramInputHandler (names : Array Name) : CommandElabM Bool := do
  let env ← getEnv
  unless names.all (fun name => (getStructureInfo? env name).isSome) do
    return false
  for name in names do
    liftTermElabM (deriveRamInput name)
  return true

initialize registerDerivingHandler ``RamInput ramInputHandler

end Complexity.Program.Deriving
