/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exists_stalkwiseFlat_epi flatCover flatCover_stalkwiseFlat flatCoverπ flatCoverπ_epi
  freePointOpenCorepresentable localSectionIndex openFree openFreeHomEquiv openFreeHomEquiv_comp
  openFreeStalkCorepresentable openFreeStalkIso openFree_stalk_flat pointOpenSections
  stalkwiseFlat stalkwiseFlat_coproduct)
end Quillen.SchemeSheaf

end
