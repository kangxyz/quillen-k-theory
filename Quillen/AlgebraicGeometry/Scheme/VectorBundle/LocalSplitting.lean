/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (exists_local_section_of_finite_basis exists_local_splitting overRestriction
  overRestriction_additive overRestriction_isLeftAdjoint overRestriction_isRightAdjoint
  shortExact_over)
end Quillen.SchemeSheaf

end
