/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Stalk.Reflection

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (closedImmersionProjectionFormulaCoefficientNatIso closedImmersionProjectionFormulaIso
  closedImmersionProjectionFormulaIso_hom closedImmersionProjectionFormulaIso_naturality_left
  closedImmersionProjectionFormulaIso_naturality_right
  closedImmersionProjectionFormulaIso_section closedImmersionProjectionFormulaModuleNatIso
  isIso_of_moduleStalk isIso_projectionFormulaMap_moduleStalk_off_image
  isIso_projectionFormulaMap_of_closedImmersion)
end Quillen.SchemeSheaf

end
