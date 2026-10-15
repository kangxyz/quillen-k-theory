/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Bilinear

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exists_scalar_two_module_germ_representatives exists_three_module_germ_representatives
  moduleTensorSectionLinear moduleTensorSection_add_left moduleTensorSection_add_right
  moduleTensorSection_smul_left moduleTensorSection_smul_right moduleTensorStalkInv
  moduleTensorStalkInv_tmul_germ moduleTensorStalkPure_add_left moduleTensorStalkPure_add_right
  moduleTensorStalkPure_smul_left moduleTensorStalkPure_smul_right)
end Quillen.SchemeSheaf

end
