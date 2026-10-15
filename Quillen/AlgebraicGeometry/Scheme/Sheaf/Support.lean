/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Support

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (isZero_iff_stalks mem_support stalkFunctor support support_eq_empty_iff support_eq_of_iso
  support_restrict supportedAway_iff_stalks supportedAway_iff_support_disjoint)
end Quillen.SchemeSheaf

end
