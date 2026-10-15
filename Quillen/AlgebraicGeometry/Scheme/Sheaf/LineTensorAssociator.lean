/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorFunctorAssociator

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (isIso_restricted_twoLineUnit isIso_twoLineUnit_tensor_sheafification
  lineTensorLeftUnitComparison lineTensorPresheafAssociator lineTensorRightUnitComparison
  moduleLineTensorAssociator)
end Quillen.SchemeSheaf

end
