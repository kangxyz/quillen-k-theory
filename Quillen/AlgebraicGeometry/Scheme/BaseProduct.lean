/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Products.IntegerBase

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Scheme.Bass
export AlgebraicGeometry.Scheme.Products
  (baseProductFunctor baseProductProjection baseProductTransformation
  baseProductTransformation_isPullback baseProductTransformation_projection
  instFlatBaseProductTransformation instIsOpenImmersionBaseProductTransformation integerBase
  qcBaseProductFunctor qcBaseProductTransformation toIntegerBase toIntegerBase_naturality)
end Quillen.Scheme.Bass

end
