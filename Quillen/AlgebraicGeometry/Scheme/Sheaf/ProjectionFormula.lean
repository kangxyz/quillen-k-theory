/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (modulePushforwardTensorMap modulePushforwardTensorMap_naturality
  modulePushforwardTensorMap_naturality_right modulePushforwardTensorMap_section
  moduleTensorRightFunctor moduleTensorRightFunctor_additive moduleTensorRightFunctor_map
  projectionFormulaMap projectionFormulaMap_eq projectionFormulaMap_naturality
  projectionFormulaMap_section projectionFormulaMap_unit projectionFormulaNatTrans
  pushforwardRingHom)
end Quillen.SchemeSheaf

end
