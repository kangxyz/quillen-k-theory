/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Strict
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Strict perfect singles in every original integer degree -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- A vector bundle in any original integer degree is strict perfect. -/
theorem single_strictPerfect_int {X : Scheme.{u}} (M : X.Modules)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M] (a : ℤ) :
    strictPerfect X ((CochainComplex.singleFunctor X.Modules a).obj M) := by
  constructor
  · refine ⟨a, a, fun n hn => ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = a
    · subst n
      simpa only [CochainComplex.singleFunctor, HomologicalComplex.single_obj_X_self] using
        (inferInstance : AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree X M)
    · exact AlgebraicGeometry.Scheme.Modules.finiteLocallyFree_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

end Quillen.PerfectComplexes
