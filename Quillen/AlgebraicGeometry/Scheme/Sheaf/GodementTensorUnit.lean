/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Tensor
public import Aglib.CategoryTheory.NatTrans.Unit

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (exactPlus_map_quasiIso godementTensorTotalUnit godementTensorTotalUnit_app
  godementTensorTotalUnit_quasiIso godementTensorUnit godementTensorUnit_app
  godementTensorUnit_quasiIso godementTotalPlus_sameLowerBound
  godementTotalPlus_termwiseFlasque)
end Quillen.SchemeSheaf

namespace Quillen.SchemeSheaf
/-- Historical name for the canonical Aglib declaration. -/
abbrev originalUnitPostcompose := @CategoryTheory.NatTrans.unitPostcompose
end Quillen.SchemeSheaf

end
