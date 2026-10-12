/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

import Quillen.KTheory.Plus.ProjectiveExtensionCartesian

/-! # Strong cartesian lifts in the actual localized extension category -/
noncomputable section
open CategoryTheory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]

example (A : IsoCategory R) {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    (localizedExtensionProjection R).IsStronglyCartesian
      ((localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f))
      (localizedExtensionOriginalHom R A f) := inferInstance

example (y : LocalizedExtensionCategory R)
    (b : Quillen.Q (exactStructure R).deflation (exactStructure R).inflation)
    (g : b ⟶ (localizedExtensionProjection R).obj y) :
    ∃ (x : LocalizedExtensionCategory R)
      (e : b ≅ (localizedExtensionProjection R).obj x) (f : x ⟶ y),
      e.hom ≫ (localizedExtensionProjection R).map f = g ∧
        (localizedExtensionProjection R).IsStronglyCartesian
          ((localizedExtensionProjection R).map f) f :=
  exists_localizedExtensionLift R y b g
