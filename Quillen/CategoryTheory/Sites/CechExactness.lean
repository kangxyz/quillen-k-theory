/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Exactness

/-! # Compatibility imports for the canonical Aglib interface -/
@[expose] public section

-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.Cech
export CategoryTheory.Cech
  (cechComplex_exactAt_succ_of_terminal_component cechCosimplicialChangeIso
  evaluatedCechAugmentation evaluatedCechExtraDegeneracy evaluatedCechUnopIso iicInclusion
  intersectFunctor intersectToId intersectToIic intersectionGaloisConnection restrictPresheaf
  restrictedCech_exactAt_succ splitCechChain_exactAt_succ splitCech_exactAt_succ)
end Quillen.Cech

end
