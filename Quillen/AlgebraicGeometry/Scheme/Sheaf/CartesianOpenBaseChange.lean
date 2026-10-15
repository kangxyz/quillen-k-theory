/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (cartesianAdjointTargetIso cartesianAdjointTargetIso_homEquiv cartesianAdjointUnitTargetIso
  cartesianAdjointUnitTargetIso_homEquiv cartesianOpenBaseChange cartesianOpenBaseChange_counit
  cartesianOpenBaseChange_homEquiv cartesianOpenBaseChange_hom_mate
  cartesianOpenBaseChange_pullback_unit cartesianOpenBaseChange_unit
  cartesianPullbackBaseChangeMate cartesianPullbackBaseChangeMate_isIso
  isIso_cartesianOpenBaseChangeUnit opensRange_of_isPullback)
end Quillen.SchemeSheaf

end
