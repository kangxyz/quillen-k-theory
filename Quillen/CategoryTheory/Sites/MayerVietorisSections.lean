/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.MayerVietorisSections

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SheafCohomology
export TopCat.Sheaf
  (sectionsComplex sectionsComplexRestriction sectionsComplexRestriction_comp
  sectionsComplexRestriction_f sectionsComplex_isLE_sup sectionsComplex_isPullback
  sectionsFunctor sectionsMayerVietoris sectionsMayerVietorisRestriction
  sectionsMayerVietoris_exact sectionsMayerVietoris_shortExact sectionsRestriction)
end Quillen.SheafCohomology

end
