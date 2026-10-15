/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (flasque_of_shortExact injectiveResolution_kernel_isFlasque injective_isFlasque
  sections_surjective_of_flasque_kernel shortExact_toSheaf toAdditiveSheaf
  toAdditiveSheaf_additive)
end Quillen.SchemeSheaf

end
