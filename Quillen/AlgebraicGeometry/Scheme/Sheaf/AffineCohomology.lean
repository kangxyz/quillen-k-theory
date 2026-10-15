/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.Vanishing

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf.AffineCech
export AlgebraicGeometry.Scheme.Modules.AffineCech
  (affineSectionPresheafFunctor affineSectionPresheafFunctor_additive
  exists_finite_principal_section_lifts_on exists_section_lift_of_cechOne_exact
  globalSections_injectiveResolution_exact_succ_of_principalCech
  injectiveResolution_kernel_principalCech_exact_succ
  isZero_rightDerived_globalSections_succ_of_principalCech
  principalCech_exactAt_succ_on_basicOpen principalCech_quotient_exact_succ
  principalCech_shortExact_of_kernel_cechOne sections_surjective_of_principalCech_exact_one
  shortExact_sections_of_surjective)
end Quillen.SchemeSheaf.AffineCech

namespace Quillen.SchemeSheaf.AffineDerived
export AlgebraicGeometry.Scheme.Modules.AffineDerived
  (globalSections_injectiveResolution_exact_succ isZero_rightDerived_globalSections_succ)
end Quillen.SchemeSheaf.AffineDerived

end
