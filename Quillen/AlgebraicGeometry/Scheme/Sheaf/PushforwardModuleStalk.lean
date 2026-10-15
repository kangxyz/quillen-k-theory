/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.Stalk

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (closedImmersionModuleStalkIso isZero_closedImmersion_moduleStalk_of_not_mem
  isZero_pushforward_moduleStalk_of_not_mem pushforwardModuleStalkIso pushforwardModuleStalkMap
  pushforwardModuleStalkMap_germ pushforwardModuleStalkMap_isIso_of_isInducing
  pushforwardModuleStalkMap_naturality)
end Quillen.SchemeSheaf

end
