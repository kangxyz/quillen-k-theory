/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.BaseChangeGluing

/-! # Original coefficient change over an open base

When the original affine base map is an open immersion, so is its genuine two-chart
coefficient change. Its image is exactly the inverse image of the original base open.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace Quillen.Scheme.ProjectiveLine
variable {R S : CommRingCat.{u}} (f : R ⟶ S) [IsOpenImmersion (Spec.map f)]

instance coefficientMap_open : IsOpenImmersion (coefficientMap f) :=
  MorphismProperty.of_isPullback (coefficientMap_isPullback f).flip inferInstance

lemma coefficientMap_opensRange :
    (coefficientMap f).opensRange = (projection R) ⁻¹ᵁ (Spec.map f).opensRange := by
  have h := (coefficientMap_isPullback f).isoPullback_hom_fst
  simpa only [h] using
    ((Scheme.Hom.opensRange_comp_of_isIso (coefficientMap_isPullback f).isoPullback.hom
      (pullback.fst (projection R) (Spec.map f))).trans
      (Scheme.Hom.opensRange_pullbackFst (Spec.map f) (projection R)))

end Quillen.Scheme.ProjectiveLine
