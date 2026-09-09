/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Linking.Basic

/-!
# Extending a source program with callers

`Program.extend` adds function bodies already typed against the combined signature table.
These bodies can call either one another or imported functions. Imported bodies retain their
own call graph through the existing signature-preserving renaming; importing them neither
executes an entry function nor replaces their implementations with specifications.

The body-selection and embedding theorems provide the frontend with the existing source
statements and the same semantic contract-transfer interface used by closed-table linking.
-/

namespace Complexity.Language.Program

/-- Add functions typed against the combined table, retaining each imported function's
actual implementation and renaming its calls to their imported positions. -/
def extend {imports : List Signature} (imported : Program imports)
    (newSignatures : List Signature)
    (newBodies : (fn : Fin newSignatures.length) →
      Stmt (newSignatures ++ imports) newSignatures[fn].params newSignatures[fn].result) :
    Program (newSignatures ++ imports) where
  body fn := by
    refine Fin.addCases
      (motive := fun index : Fin (newSignatures.length + imports.length) =>
        Stmt (newSignatures ++ imports)
          (newSignatures ++ imports)[index.cast
            (List.length_append (as := newSignatures) (bs := imports)).symm].params
          (newSignatures ++ imports)[index.cast
            (List.length_append (as := newSignatures) (bs := imports)).symm].result)
      ?_ ?_ (fn.cast (List.length_append (as := newSignatures) (bs := imports)))
    · intro index
      exact cast (congrArg
        (fun signature => Stmt (newSignatures ++ imports) signature.params signature.result)
        ((SignatureMap.appendLeft newSignatures imports).signature_eq index).symm)
        (newBodies index)
    · intro index
      exact cast (congrArg
        (fun signature => Stmt (newSignatures ++ imports) signature.params signature.result)
        ((SignatureMap.appendRight newSignatures imports).signature_eq index).symm)
        ((imported.body index).renameCalls (SignatureMap.appendRight newSignatures imports))

/-- Selecting an added function returns the supplied body without renaming its calls. -/
theorem extend_body {imports : List Signature} (imported : Program imports)
    (newSignatures : List Signature)
    (newBodies : (fn : Fin newSignatures.length) →
      Stmt (newSignatures ++ imports) newSignatures[fn].params newSignatures[fn].result)
    (fn : Fin newSignatures.length) :
    (SignatureMap.appendLeft newSignatures imports).body
      (imported.extend newSignatures newBodies) fn = newBodies fn := by
  simp [SignatureMap.body, extend, SignatureMap.appendLeft]

/-- Adding callers preserves all imported function bodies through the original typed map. -/
theorem embeds_extend {imports : List Signature} (imported : Program imports)
    (newSignatures : List Signature)
    (newBodies : (fn : Fin newSignatures.length) →
      Stmt (newSignatures ++ imports) newSignatures[fn].params newSignatures[fn].result) :
    imported.Embeds (SignatureMap.appendRight newSignatures imports)
      (imported.extend newSignatures newBodies) := by
  intro fn
  dsimp only [SignatureMap.body, extend, SignatureMap.appendRight]
  change cast _ (Fin.addCases
    (motive := fun index : Fin (newSignatures.length + imports.length) =>
      Stmt (newSignatures ++ imports)
        (newSignatures ++ imports)[index.cast
          (List.length_append (as := newSignatures) (bs := imports)).symm].params
        (newSignatures ++ imports)[index.cast
          (List.length_append (as := newSignatures) (bs := imports)).symm].result)
    _ _ (Fin.natAdd newSignatures.length fn)) = _
  rw [Fin.addCases_right]
  simp only [cast_cast, cast_eq]

end Complexity.Language.Program
