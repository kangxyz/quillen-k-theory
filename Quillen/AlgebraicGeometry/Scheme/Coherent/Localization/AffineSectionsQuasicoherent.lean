/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsQuasicoherent

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.AffineSections
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
  (exists_pow_smul_eq_zero exists_pow_smul_extension isLocalizing_pushforward_of_isCompact
  isQuasicoherent_pushforward_of_isCompact isQuasicoherent_restrict_pushforward_opensRange)
end Quillen.CoherentScheme.AffineSections

end
