/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Exact filtered colimits for integral local coefficients

The coefficient modules may live in an arbitrary universe although the ring
of integers is small. The underlying algebraic theorems are owned by
`ModuleCat` and the homological-complex API. The resulting homology comparison is algebraic: a
geometric chain-colimit identification is still required before applying it
to filtered spaces or telescopes.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace Quillen.LocalCoefficients

/-- Compatibility name for exact filtered colimits in arbitrary module universes. -/
alias moduleCategoryAB5 := ModuleCat.ab5

variable (J : Type u) [SmallCategory J] [IsFiltered J]

/-- The actual filtered-colimit functor preserves kernels and cokernels. -/
theorem filteredColimit_preservesHomology :
    (colim : (J ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ).PreservesHomology :=
  ModuleCat.colim_preservesHomology ℤ J

/-- Homology of an actual filtered colimit of short complexes agrees with
colimit of homology; no topological comparison is assumed here. -/
def filteredColimitHomologyIso (S : ShortComplex (J ⥤ ModuleCat.{u} ℤ)) :
    (S.map (colim : (J ⥤ ModuleCat.{u} ℤ) ⥤ ModuleCat.{u} ℤ)).homology ≅
      colim.obj S.homology := by
  letI := filteredColimit_preservesHomology J
  exact S.mapHomologyIso colim

end Quillen.LocalCoefficients
