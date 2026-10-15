/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (finiteLocalBasis_bind finiteLocalBasis_of_sheafIso finiteLocalBasis_over_of_restrict
  finiteLocallyFree_iff_schemeOpenCover finiteLocallyFree_of_affineCharts
  finiteLocallyFree_of_openCover finiteLocallyFree_of_openImmersionCover
  finiteLocallyFree_of_schemeOpenCover finiteLocallyFree_restrict_opensRange
  presentationMap_generators_isIso presentationOfIsIso_generators_isIso)
end Quillen.SchemeSheaf

end
