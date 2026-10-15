/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineFiniteSheaf_exists_generatingSections affineFiniteSheaf_iff_exists_generatingSections
  affineFiniteSheaf_of_presentation affineFiniteSheaf_restrict
  finite_globalSections_of_generatingSections finite_globalSections_of_presentation)
end Quillen.CoherentScheme

end
