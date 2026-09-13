/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Complexity.Language.Syntax.Core
import Complexity.Language.Syntax.Represented

/-!
# High-level source syntax

This public import provides the source declaration, mathematical data views and
their checked correspondence interfaces together. Container implementations and
compiler support import `Syntax.Core` directly, so defining the operations used
by this frontend does not depend on importing the frontend itself.

All declarations use the same typed source emitter and registered source
identities. Existing explicit proof-view forms remain available; sharing this
import does not by itself complete general represented control-flow lowering.
See the high-level language guide for the supported operations and proof views.
-/
