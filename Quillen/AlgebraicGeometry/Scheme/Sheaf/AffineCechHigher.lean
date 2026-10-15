/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.AffineHigherExactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf.AffineCech
export AlgebraicGeometry.Scheme.Modules.AffineCech
  (basicOpen_finset_prod principalCechComplex principalCechRestriction
  principalCechRestriction_isLocalized principalCech_exactAt_succ
  principalCech_exactAt_succ_away principalCech_exactAt_succ_of_isUnit principal_product_eq)
end Quillen.SchemeSheaf.AffineCech

end
