/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sheafification

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (isIso_line_tensor_sheafificationUnit isIso_restricted_unit_of_iso_sheaf
  isIso_sheafified_restricted_unit restrictionSheafificationIso)
end Quillen.SchemeSheaf

end
