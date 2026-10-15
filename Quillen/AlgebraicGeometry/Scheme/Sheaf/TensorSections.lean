/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (moduleTensorCoefficientMap_section moduleTensorLeftFunctor_map_section moduleTensorSection
  moduleTensorSection_restrict moduleTensor_hom_ext tensorRestrictionIso_section)
end Quillen.SchemeSheaf

end
