/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.DegreeZero

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (difference_homologyZero_naturality pairHomologyZeroIso pair_toRightDerivedZero_isIso
  resolutionHomologyZeroMap resolutionHomologyZeroMap_naturality
  sectionsFunctor_preservesFiniteLimits sectionsHomologyZeroIso)
end Quillen.SchemeSheaf

end
