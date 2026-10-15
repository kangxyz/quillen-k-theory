/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Section.Span

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (pushforwardPlusUnit_quasiIso_of_flasque sectionComplexPlusIso sectionRepeatedTotalImage
  sectionSourceTotalToRepeated sectionSourceTotalToRepeated_quasiIso sectionTotalImage
  sectionTotalPlus_isFlasque sectionTotalToRepeated sectionTotalToRepeated_quasiIso)
end Quillen.SchemeSheaf

end
