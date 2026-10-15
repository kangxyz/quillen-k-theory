/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (hom_eq_of_globalSections_eq tildePullbackIso_globalSections_unit tildePullbackIso_unit
  tildePushforwardIso_globalSections tildePushforwardIso_globalSections_unit)
end Quillen.SchemeSheaf

end
