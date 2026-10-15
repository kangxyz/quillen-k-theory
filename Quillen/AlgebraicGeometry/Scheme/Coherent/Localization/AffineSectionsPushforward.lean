/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsPushforward

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.AffineSections
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
  (isIso_pushforward_modulesSpecToSheaf_map_inf
  isIso_pushforward_modulesSpecToSheaf_map_inf_opensRange
  isIso_pushforward_modulesSpecToSheaf_map_of_preimage_eq
  isIso_pushforward_presheaf_map_inf_opensRange isQuasicoherent_restrict_pushforward)
end Quillen.CoherentScheme.AffineSections

end
