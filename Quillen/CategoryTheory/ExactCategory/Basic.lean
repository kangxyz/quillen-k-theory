/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic

/-!
# Exact-category compatibility names

The general exact-category interface is owned by Aglib. These transparent names
keep the Quillen application API while sharing the canonical structures and instances.
-/
@[expose] public section

namespace Quillen

export CategoryTheory.ExactCategory (ExactStructure)

namespace Conflations
export CategoryTheory.ExactCategory.Conflations (inflation deflation)
end Conflations

namespace ExactStructure
export CategoryTheory.ExactCategory.ExactStructure
  (inflation deflation inflation_of_conflation deflation_of_conflation
    mono_of_inflation epi_of_deflation inflation_of_isKernel deflation_of_isCokernel
    inflation_zero deflation_zero inflation_of_isPullback)
end ExactStructure

end Quillen
