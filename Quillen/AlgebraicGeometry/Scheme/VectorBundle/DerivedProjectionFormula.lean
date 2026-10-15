/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (derivedProjectionFormulaIso derivedProjectionFormulaIso_unit projectionFormulaNatIso
  projectionFormulaNatIso_hom_app tensorPushforwardDerivedCompIso
  tensorPushforwardDerivedCompIso_unit)
end Quillen.SchemeSheaf

end
