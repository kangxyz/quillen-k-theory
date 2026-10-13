/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.KTheory.Plus.ProjectiveExtensionProjection

/-! # The actual localized extension comparison projection -/
noncomputable section
open CategoryTheory MonoidalCategory
open Quillen.FiniteProjectiveModule
universe u
variable (R : Type u) [Ring R]

example : LocalizedExtensionCategory R ⥤
    Quillen.Q (exactStructure R).deflation (exactStructure R).inflation :=
  localizedExtensionProjection R

example (A : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    (localizedExtensionProjection R).obj (localizedExtensionPair R A x) =
      (exactStructure R).extensionProjectionQObj x :=
  localizedExtensionProjection_obj R A x

example (x : LocalizedExtensionCategory R) :
    (localizedExtensionProjection R).map (𝟙 x) = 𝟙 _ :=
  (localizedExtensionProjection R).map_id x

example {x y z : LocalizedExtensionCategory R} (f : x ⟶ y) (g : y ⟶ z) :
    (localizedExtensionProjection R).map (f ≫ g) =
      (localizedExtensionProjection R).map f ≫ (localizedExtensionProjection R).map g :=
  (localizedExtensionProjection R).map_comp f g
