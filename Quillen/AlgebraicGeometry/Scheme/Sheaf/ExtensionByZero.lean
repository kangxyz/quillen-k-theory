/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.ExtensionByZero

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (extensionByZero extensionByZeroFullyFaithful extensionByZeroModuleStalkIso
  extensionByZeroRestrictAdjunction extensionByZeroRestrictIso extensionByZeroTriple
  extensionByZero_additive extensionByZero_faithful extensionByZero_full
  extensionByZero_isLeftAdjoint extensionByZero_preservesFiniteLimits
  extensionByZero_preservesMonomorphisms extensionByZero_unit_isIso
  isZero_extensionByZero_stalk_of_not_mem isZero_restrict_moduleSkyscraper_of_not_mem
  mono_extensionByZero_map restrict_extensionByZero_counit_isIso shortExact_extensionByZero
  stalkwiseFlat_extensionByZero)
end Quillen.SchemeSheaf

end
