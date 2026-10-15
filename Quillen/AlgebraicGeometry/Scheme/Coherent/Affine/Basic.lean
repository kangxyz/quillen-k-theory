/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Basic
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CoherentScheme
export AlgebraicGeometry.Scheme.Modules.QuasiCoherent
  (AffineFiniteType AffineQuasicoherent affineFiniteType affineFiniteTypeModuleEquivalence
  affineFiniteTypeToModules affineFiniteType_essentiallySmall affineFiniteType_iff
  affineFiniteType_isoClosed affineQuasicoherent_hasFiniteLimits instAbelianAffineQuasicoherent)
export AlgebraicGeometry.Scheme.Modules.Coherent
  (affineCoherentExactStructure affineFiniteType_isSerreClass instAbelianAffineCoherent)
end Quillen.CoherentScheme

end
