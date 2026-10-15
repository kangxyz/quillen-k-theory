/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (FiniteLocallyFree FinitePresentation IsFiniteLocallyFree finiteFree finiteLocallyFree
  finiteLocallyFreeForget finiteLocallyFreeToFinitePresentation
  finiteLocallyFreeToFinitePresentation_comp_forget finiteLocallyFree_closedUnderIsomorphisms
  finiteLocallyFree_containsZero finiteLocallyFree_free finiteLocallyFree_iff_of_iso
  finiteLocallyFree_le_finitePresentation finiteLocallyFree_obj finiteLocallyFree_of_isZero
  finiteLocallyFree_of_iso finiteLocallyFree_zero finitePresentation finitePresentationForget
  finitePresentation_closedUnderIsomorphisms finitePresentation_containsZero
  finitePresentation_free finitePresentation_iff_of_iso finitePresentation_map_isFinite
  finitePresentation_obj finitePresentation_of_isZero finitePresentation_of_localBasis
  finitePresentation_of_presentation generatingSections_ofEpi_isIso
  isFinitePresentation_of_finiteLocallyFree isLocallyFree_of_finiteLocallyFree
  isQuasicoherent_of_finitePresentation isZero_free_empty localBasisOfIso
  localBasisOfIso_isFiniteType localBasisOfIso_isLocallyFreeData ofFiniteLocallyFree
  ofFinitePresentation)
end Quillen.SchemeSheaf

end
