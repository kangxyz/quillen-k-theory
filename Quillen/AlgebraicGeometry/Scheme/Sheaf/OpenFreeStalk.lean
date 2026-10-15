/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeStalk

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (corepresentable_uniqueUpToIso_homEquiv openFreeStalkCorepresentable_naturality
  openFreeStalkIso_naturality openFreeStalkNatIso openFreeStalk_map_isIso pointMembershipFunctor
  pointOpenFreeFunctor)
end Quillen.SchemeSheaf

end
