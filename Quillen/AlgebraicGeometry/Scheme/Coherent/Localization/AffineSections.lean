/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSections

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.AffineSections
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections
  (ClearsDenominators clearsDenominators_basicOpen clearsDenominators_iff_isLocalized
  isLocalized_of_isCompact isLocalized_of_principal_charts
  principal_chart_quasicoherent_of_restrict restriction)
end Quillen.CoherentScheme.AffineSections

namespace Quillen.CoherentScheme.AffineSections.ClearsDenominators
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections.ClearsDenominators
  (of_finite_cover)
end Quillen.CoherentScheme.AffineSections.ClearsDenominators

end
