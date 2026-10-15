/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pushforward.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (closedImmersionExactPushforward epi_of_moduleStalk epi_pushforward_of_isClosedEmbedding
  pushforward_preservesEpimorphisms_of_closedImmersion
  pushforward_preservesFiniteColimits_of_closedImmersion
  shortExact_pushforward_of_closedImmersion)
end Quillen.SchemeSheaf

end
