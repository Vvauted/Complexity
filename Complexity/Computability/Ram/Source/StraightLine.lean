/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Source.Basic

/-!
# Straight-line source statements

`Ram.Stmt.IsStraightLine` identifies sequences of primitive operations, without branches,
loops or function calls. It describes only the program's syntax: reads may still require
input, and memory operations retain their usual safety obligations.
-/

namespace Ram.Stmt

/-- A statement built from primitive operations and sequencing, with no control-flow
branches, loops or function calls. -/
def IsStraightLine : Stmt → Prop
  | .skip | .assign .. | .store .. | .read .. | .write .. => True
  | .seq first second => first.IsStraightLine ∧ second.IsStraightLine
  | .ite .. | .while .. | .call .. => False

end Ram.Stmt
