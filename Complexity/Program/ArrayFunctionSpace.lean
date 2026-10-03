/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ArrayFunctionSpace

/-!
# Single-array physical-space interface

Focused public entry for the single-array space API and its definitionally
identical `toProgram` certificates. The metric is initialized input union actual
heap accesses, not reserved capacity or peak-live memory.
-/
