/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Exact

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exactRestrict restrictFunctor_additive restrictFunctor_isLocalization
  restrictFunctor_isRightAdjoint sheafExactStructure supportedAway supportedAway_iff
  supportedAway_iff_of_shortExact supportedAway_isSerreClass supportedAway_isoModSerre_iff)
end Quillen.SchemeSheaf

end
