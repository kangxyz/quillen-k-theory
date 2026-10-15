/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineFiniteSheaf affineFiniteSheaf_eq_essImage affineFiniteSheaf_isoClosed)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineFiniteSheaf_containsZero affineFiniteSheaf_finiteColimits
  affineFiniteSheaf_finiteLimits)
end Quillen.CoherentScheme

end
