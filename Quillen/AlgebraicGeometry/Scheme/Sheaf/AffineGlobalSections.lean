/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.GlobalSectionsExactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf.AffineCech
export AlgebraicGeometry.Scheme.Modules.AffineCech
  (epi_globalSections_of_quasicoherent_kernel exists_finite_principal_section_lifts
  exists_global_lift_of_principal_lifts exists_global_section_lift globalSections_isRightAdjoint
  mapSection mapSection_injective mapSection_res mapSection_zero_comp section_lift_of_shortExact
  shortExact_globalSections_of_quasicoherent_kernel)
end Quillen.SchemeSheaf.AffineCech

end
