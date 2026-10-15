/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.CoefficientBaseChange
export AlgebraicGeometry.Scheme.BaseChange.Coefficients
  (Index coefficientProjection compactSpace_space functor identityProjectionIso
  identityProjectionIso_schemeMap map map_coefficientProjection map_comp map_id map_projection
  projection quasiSeparatedSpace_space row rowTransformation schemeMap
  schemeMap_coefficientProjection schemeMap_isOpenImmersion schemeMap_isPullback
  schemeMap_projection space)
end Quillen.Scheme.CoefficientBaseChange

end
