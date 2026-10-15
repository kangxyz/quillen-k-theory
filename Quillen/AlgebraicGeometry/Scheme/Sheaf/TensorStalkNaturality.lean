/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Naturality

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleStalk_map_germ moduleTensorLeftStalkIso moduleTensorLeftStalkIso_coefficient_naturality
  moduleTensorStalkIso_naturality_left moduleTensorStalkIso_naturality_right)
end Quillen.SchemeSheaf

end
