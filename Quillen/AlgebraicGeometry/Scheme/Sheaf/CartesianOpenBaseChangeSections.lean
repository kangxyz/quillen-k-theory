/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.CartesianSections

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (cartesianOpenBaseChange_hom_app cartesianOpenBaseChange_hom_app_mate
  cartesianPushforwardSquare_hom_app restrictFunctor_map_app)
end Quillen.SchemeSheaf

end
