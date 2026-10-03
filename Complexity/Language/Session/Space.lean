/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceFinite
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceLoaders
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePhaseBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceTraceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpaceScheduledTraceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedTraceBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedHistoryBound
import Complexity.Computability.Ram.Compiler.Language.Session.SpacePreparedWorstCaseBound

/-!
# Space bounds for persistent sessions

Public finite, uniform, scheduled and prepared-session space interfaces. Each
callback retains the actual state and heap and extends a physical-address union;
neither the seed nor the footprint is reset between calls. Preparation relations
are fixed by the interface author and must describe the real loader execution.
Concrete buffer and list preparation certificates are available through their
focused `Buffer.PrepareSpace` and `List.PrepareSpace` imports.
-/
