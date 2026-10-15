/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineCoherentInclusion affineCoherentToQuasicoherent_preservesFiniteColimits
  affineCoherentToQuasicoherent_preservesFiniteLimits affineCoherent_shortExact_iff
  affineFiniteTypeToModules_additive affineFiniteTypeToModules_preservesFiniteColimits
  affineFiniteTypeToModules_preservesFiniteLimits)
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineQuasicoherentToSheavesIso affineQuasicoherentToSheaves_preservesFiniteColimits
  affineQuasicoherentToSheaves_preservesFiniteLimits)
end Quillen.CoherentScheme

end
