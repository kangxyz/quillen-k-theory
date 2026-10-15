/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.FiniteLocalization

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.FiniteModuleLocalization
export ModuleCat.FiniteLocalization
  (functor functor_additive functor_comp_forget functor_map_hom functor_obj_obj
  functor_preservesFiniteColimits functor_preservesFiniteLimits isoModSerre_iff torsion
  torsion_iff torsion_iff_elementwise torsion_iff_uniform torsion_isSerreClass
  torsion_powers_iff_elementwise torsion_powers_iff_uniform)
end Quillen.FiniteModuleLocalization

end
