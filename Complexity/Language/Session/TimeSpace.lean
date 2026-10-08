/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.TimeSpace
import Complexity.Computability.Ram.Compiler.Language.Session.TimeSpace.Stateful

/-!
# Joint resources for persistent sessions

Public entry point for same-execution instruction and physical-word bounds,
including fixed histories, accepted traces, prepared requests and schedules.
Uniform contracts retain one admitted word width for the entire session;
fixed-width contracts use explicit budgets. Preparation observes the actual
loader, and source correctness remains independent of resource bounds.
-/
