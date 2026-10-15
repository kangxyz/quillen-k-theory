/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (affineLocallyFiniteType_spec_eq_affineFiniteSheaf affineLocallyFiniteType_spec_iff
  finiteTypeSheavesAffineEquivalence finiteTypeSheavesAffineEquivalence_comp_inclusion
  finiteTypeSheavesSpecModuleEquivalence finiteTypeSheavesSpec_essentiallySmall)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineToCoherentExact coherentToAffineExact finiteTypeSheavesAffineEquivalence_additive
  finiteTypeSheavesAffineEquivalence_inverse_additive
  finiteTypeSheavesSpecModuleEquivalence_inverse_additive)
end Quillen.CoherentScheme

end
