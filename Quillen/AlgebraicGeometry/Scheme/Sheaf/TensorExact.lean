/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleTensorCoefficientMap moduleTensorCoefficientMap_app moduleTensorCoefficientMap_comp
  moduleTensorCoefficientMap_id moduleTensorLeftFunctor moduleTensorLeftFunctor_additive
  pullbackFiniteFreeRetract pullbackFiniteFreeRetract_i pullbackFiniteFreeRetract_r
  tensor_shortExact_pullback_finiteFreeRetract)
end Quillen.SchemeSheaf

end
