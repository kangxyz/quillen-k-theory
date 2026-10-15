/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Complex

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (acyclicComplex_kernel_isFlasque biprod_isFlasque flasque_of_iso mappingCone_isFlasque
  prod_isFlasque pushforward_exactAt_succ_of_acyclic_flasque quasiIso_pushforward_of_flasque)
end Quillen.SchemeSheaf

end
