/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Pullback

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleFlat_of_shortExact shortExact_extendScalars_of_flat_quotient
  shortExact_pullback_of_stalkwiseFlat_quotient stalkwiseFlat_of_shortExact
  stalkwiseFlat_pullback)
end Quillen.SchemeSheaf

end
