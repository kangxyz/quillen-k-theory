/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Stalk

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (isIso_projectionFormulaMap_moduleStalk_of_isInducing projectionFormulaMap_stalk_comparison
  projectionFormulaStalkSourceIso projectionFormulaStalkSourceIso_germ
  projectionFormulaStalkTargetIso projectionFormulaStalkTargetIso_unit_germ)
end Quillen.SchemeSheaf

end
