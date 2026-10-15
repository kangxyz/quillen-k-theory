/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Localization

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (sectionDerivedUnitComparison sectionSourceTotalToRepeatedDerivedIso
  sectionTotalDerivedComparison sectionTotalDerivedComparisonNat
  sectionTotalDerivedComparisonNat_app sectionTotalToRepeated_derivedComparison
  sectionTotalToRepeated_localized sourceTotalAugmentationDerivedIso)
end Quillen.SchemeSheaf

end
