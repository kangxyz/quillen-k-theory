/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.FirstCohomology

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (difference_firstConnecting firstCohomologySequence firstCohomologySequence_exact
  firstConnecting firstConnecting_epi_of_affine_cover
  firstConnecting_twoAffineRightDerivedOneIsoCokernel_hom twoAffineRightDerivedOneIsoCokernel
  twoAffine_isZero_rightDerived_one_of_difference_surjective)
end Quillen.SchemeSheaf

end
