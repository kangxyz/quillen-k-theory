/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.IdealClosedSupport

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.FiniteModuleLocalization.IdealClosedSupport
export ModuleCat.FiniteLocalization.IdealClosedSupport
  (ClosedRing closedEquivalence closedEquivalence_comp_inclusion closedRestriction
  closedRestrictionExact closedRestriction_additive closedRestriction_faithful
  closedRestriction_full closedRestriction_killed closedRestriction_map_hom
  closedRestriction_obj_obj closedRestriction_preservesFiniteColimits
  closedRestriction_preservesFiniteLimits closedToKilled closedToKilledExact
  closedToKilled_additive closedToKilled_essSurj closedToKilled_faithful closedToKilled_full
  closedToKilled_isEquivalence fullyFaithfulClosedRestriction instAbelianKilledBy killedBy
  killedBy_iff_isTorsionBySet killedBy_iff_le_annihilator killedBy_isoClosed
  killedInclusionComparison killedInclusionExact killedInclusion_preservesFiniteColimits
  killedInclusion_preservesFiniteLimits killed_hasFiniteProducts)
end Quillen.FiniteModuleLocalization.IdealClosedSupport

end
