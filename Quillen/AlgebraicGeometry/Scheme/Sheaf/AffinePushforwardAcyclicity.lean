/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (affinePushforward_injectiveResolution_exact_succ isAffineOpen_injectiveResolution_exact_succ
  isZero_rightDerived_pushforward_succ)
end Quillen.SchemeSheaf

end
