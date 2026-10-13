/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.Homotopy
public import Quillen.Topology.HELP.Basic

/-!
# The literal one-point prespectrum

The auxiliary point object has the actual singleton in every degree and constant structure
loops. Its unchanged point inclusion has HEP as an identity map. This concrete object is used
to compare an original reduced pushout with an original reduced mapping cone.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- The actual singleton prespectrum, with literal constant based structure loops. -/
def pointPrespectrum : LoopPrespectrum.{u} where
  space _ := TopCat.of PUnit.{u + 1}
  point _ := PUnit.unit
  structureMap _ := ContinuousMap.const _ (Path.refl PUnit.unit)
  map_point _ := rfl

/-- The literal chosen point of the singleton prespectrum has HEP in every level. -/
theorem pointPrespectrum_point_homotopyExtensionProperty (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} (pointPrespectrum.{u}.point n))) := by
  have he : TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (pointPrespectrum.{u}.point n)) =
      𝟙 (TopCat.of PUnit.{u + 1}) := by
    ext x
    change (PUnit.unit : PUnit.{u + 1}) = x
    exact Subsingleton.elim _ _
  rw [he]
  exact Quillen.homotopyExtensionProperty_of_isIso _

end Quillen.LoopPrespectrum
