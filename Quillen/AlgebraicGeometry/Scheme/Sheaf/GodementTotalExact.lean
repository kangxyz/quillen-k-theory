/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Exactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (GodementTotalDegree godementDiagonalFunctor godementDiagonalFunctor_additive
  godementDiagonalFunctor_preservesHomology godementDiagonalFunctor_shortExact
  godementResolutionInt_preservesHomology godementResolutionInt_shortExact
  godementTotalDegreeIso godementTotal_additive godementTotal_map_degreewiseMono
  godementTotal_preservesFiniteColimits godementTotal_preservesFiniteLimits
  godementTotal_preservesHomology godementTotal_shortExact godement_discrete_shortExact)
end Quillen.SchemeSheaf

end
