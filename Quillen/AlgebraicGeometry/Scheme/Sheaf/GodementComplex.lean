/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Basic

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules.Godement
  (GodementFiniteDegree godementBicomplex godementBicomplex_d₁_zeroRow godementBicomplex_germ_d₂
  godementBicomplex_isZero_offDiagonal godementFiniteDiagonal godementFiniteToTotal
  godementIntGerm godementIntGerm_d godementIntGerm_naturality godementResolutionInt
  godementResolutionIntUnit godementResolutionIntUnit_quasiIso godementResolutionIntXIso
  godementResolutionInt_additive godementResolutionInt_isFlasque
  godementResolutionInt_isStrictlyGE godementResolutionInt_isZero godementTotal
  godementTotalFiniteIso godementTotalPlus godementTotalPlus_derivedPushforwardUnit_isIso
  godementTotalToFinite godementTotalUnit godementTotal_isFlasque godementTotal_isStrictlyGE
  godement_finiteBiproduct_isFlasque godement_isFlasque_of_isZero)
end Quillen.SchemeSheaf

end
