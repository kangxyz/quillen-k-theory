/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.DerivedGlobalSections

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf.AffineDerived
export AlgebraicGeometry.Scheme.Modules.AffineDerived
  (globalSections_injectiveResolution_exact_one
  globalSections_injectiveResolution_exact_succ_of_flasque
  isZero_rightDerived_globalSections_one isZero_rightDerived_globalSections_succ_of_flasque)
end Quillen.SchemeSheaf.AffineDerived

end
