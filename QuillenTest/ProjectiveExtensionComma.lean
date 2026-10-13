/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.Topology.ClassifyingSpace.ProjectiveExtensionComma

/-! # Actual fiber-to-comma homotopy equivalence, without a transition assumption -/
noncomputable section
open CategoryTheory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]

example (b : Quillen.Q (exactStructure R).deflation (exactStructure R).inflation) :
    (Quillen.IsoFiber.toStructured (localizedExtensionProjection R) b).IsLeftAdjoint :=
  inferInstance

example : ContinuousMap.HomotopyEquiv
    (Quillen.ClassifyingSpace (GroupCompletionCategory R))
    (Quillen.ClassifyingSpace
      (StructuredArrow (exactStructure R).qZero (localizedExtensionProjection R))) :=
  completionZeroCommaClassifyingHomotopyEquiv R
