/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.HomotopyCategory.Plus.BoundedComparison

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.CochainComplex
export CochainComplex
  (brutalLayerTriangle brutalLayerTriangle_distinguished brutalPlus brutalPlus_isZero
  isIso_app_brutal_of_upper_bound isIso_app_brutal_step isIso_app_of_term_bounds
  isIso_app_single_of_zero singlePlus)
end Quillen.CochainComplex

end
