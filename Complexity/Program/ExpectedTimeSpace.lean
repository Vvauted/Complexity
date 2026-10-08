/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.ExpectedTimeSpace
import Complexity.Computability.Ram.Compiler.Language.Program.ExpectedTimeSpace.Pointwise

/-!
# Expected time and samplewise space

Public entry point for actual execution costs under specified input laws,
including fixed-parameter and input-dependent targets. These contracts do not
add internal random sampling or weaken independent functional correctness.
-/
