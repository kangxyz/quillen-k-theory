/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exists_finiteGlobalBasis_of_free_sections finiteLocallyFree_tilde_iff_projective
  finiteLocallyFree_tilde_of_finite_projective free_globalSections_of_basis
  free_restrictPrincipal_of_overBasis generatingSectionsPrincipalToOver
  generatingSectionsPrincipalToOver_isFiniteType generatingSectionsPrincipalToOver_isIso
  generatingSectionsRestrictToOver generatingSectionsRestrictToOver_isFiniteType
  generatingSectionsRestrictToOver_isIso projective_of_finiteLocallyFree_tilde)
end Quillen.SchemeSheaf

end
