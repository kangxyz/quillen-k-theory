/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (godementTotalPlusUnit godementTotalPlusUnit_quasiIso godementTotalPlus_map_quasiIso
  godementTotalUnit_quasiIso godementTotalUnit_quasiIso_of_isStrictlyGE)
end Quillen.SchemeSheaf

end
