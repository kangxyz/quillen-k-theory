/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.FiniteRestrictionScalars

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme.FiniteAffine
export ModuleCat.FiniteRestrictionScalars
  (moduleRestriction moduleRestrictionExact moduleRestriction_additive moduleRestriction_map
  moduleRestriction_obj moduleRestriction_preservesFiniteColimits
  moduleRestriction_preservesFiniteLimits)
end Quillen.CoherentScheme.FiniteAffine

end
