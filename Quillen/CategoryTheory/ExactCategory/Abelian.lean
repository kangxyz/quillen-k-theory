/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.CategoryTheory.ExactCategory.Basic

/-! # Compatibility names for the canonical abelian exact structure -/
@[expose] public section

namespace Quillen
export CategoryTheory.ExactCategory
  (abelianExactStructure shortExact_inflation_iff shortExact_deflation_iff
    shortExact_inflation_eq_monomorphisms
    shortExact_deflation_eq_epimorphisms abelianExactStructure_conflation
      abelianExactStructure_inflation_iff
    abelianExactStructure_deflation_iff)
end Quillen
