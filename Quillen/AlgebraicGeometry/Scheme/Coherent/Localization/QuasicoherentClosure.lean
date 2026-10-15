/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineQuasicoherent_exists_presentation affineQuasicoherent_finiteColimits
  affineQuasicoherent_finiteLimits quasicoherent_cokernel quasicoherent_finiteColimits
  quasicoherent_finiteLimits quasicoherent_iff_affineCharts quasicoherent_kernel
  quasicoherent_of_affineCharts)
end Quillen.CoherentScheme

end
