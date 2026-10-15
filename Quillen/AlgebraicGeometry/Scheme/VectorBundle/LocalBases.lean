/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalBases

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (finiteLocallyFree_iff_pointwise over_sections_ext restrictLocalBasis
  restrictLocalBasis_isFiniteType restrictLocalBasis_isIso restrictLocalBasis_s_top sectionOver
  sectionOver_eval sectionOver_top sectionsMap_over_sectionOver)
end Quillen.SchemeSheaf

end
