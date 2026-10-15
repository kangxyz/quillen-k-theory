/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineLocallyFiniteType_iff_finitePresentation affineLocallyFiniteType_of_binary_openCover)
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineLocallyFiniteType_of_finitePresentation)
export AlgebraicGeometry.Scheme.Modules
  (finitePresentation_of_openCover finitePresentation_over_of_restrict
  finitePresentation_pushforward_of_isLeftAdjoint finitePresentation_restrict)
end Quillen.CoherentScheme

end
