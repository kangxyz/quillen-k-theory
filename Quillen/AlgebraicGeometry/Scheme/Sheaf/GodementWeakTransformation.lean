/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PlusQuasiIso
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Naturality

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Plus
  (plus_natIso_hom_quasiIso plus_nattrans_comp_quasiIso)
export AlgebraicGeometry.Scheme.Modules.Godement
  (plus_whiskerTotalImage_quasiIso)
end Quillen.SchemeSheaf

end
