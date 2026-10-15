/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.CategoryTheory.SmallModel.Exact
public import Quillen.CategoryTheory.ExactCategory.Abelian

/-! # Compatibility names for standard abelian exact small models -/
@[expose] public section

namespace Quillen
export CategoryTheory.ExactCategory
  (shortExact_map_equivalence_iff abelianExactStructure_ofEquivalence
    abelianExactStructure_smallModel)
end Quillen
