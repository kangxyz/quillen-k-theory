/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineFiniteType_restriction affinePrincipalRestriction affinePrincipalRestrictionSquare
  affinePrincipalRestriction_comp_inclusion affineQuasicoherentRestriction
  localizationRestrictionIso localizationRestrictionIso_hom_apply localizationRestrictionNatIso
  principalOpen principalRestrictionGlobalSectionsIso restrictionGlobalSections
  restrictionGlobalSectionsEquiv restrictionGlobalSectionsFunctor
  restrictionGlobalSections_isLocalized toRestrictionGlobalSections
  toRestrictionGlobalSections_natural)
end Quillen.CoherentScheme

end
