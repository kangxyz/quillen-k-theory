/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PushforwardComposition

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (derivedPushforwardComp_isRightDerived derivedPushforwardFunctorCompIso
  derivedPushforwardFunctorCompIso_unit derivedPushforwardPlusCompIso
  derivedPushforwardPlusCompIso_unit)
end Quillen.SchemeSheaf

end
