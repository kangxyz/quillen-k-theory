/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.TensorPushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (isIso_derivedPushforwardPlusUnit_tensor_injective isIso_moduleTensorLeft_derivedUnit
  moduleTensorLeft_preservesHomology tensorPushforward_isRightDerived)
end Quillen.SchemeSheaf

end
