/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.InjectiveCoefficients

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (affine_injectiveCech_exact_succ injectiveCech_exact_succ openFreeCechComplex
  openFreeCechComplex_exact_succ openFreeHomAddEquiv openFreeHomEquiv_add openFreeYonedaIso
  openFree_stalkCech_exact_succ openFree_stalkCech_exact_succ_any
  openFree_stalk_isZero_of_not_mem shortComplex_exact_of_moduleStalk)
end Quillen.SchemeSheaf

end
