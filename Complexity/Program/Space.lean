/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Program.Space
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceTime
import Complexity.Computability.Ram.Compiler.Language.Program.SpaceMeasured

/-!
# Public program physical-space interface

Finite and asymptotic bounds observe the fixed preloaded input arena prefix,
including any padding, and distinct
physical heap words accessed by the same compiled program. Time/space joins
identify one actual execution. This is not exact peak-live storage, an address
capacity limit, or the extra memory usage of a host preprocessor/interpreter.
The preloaded input arena itself is included.
-/
