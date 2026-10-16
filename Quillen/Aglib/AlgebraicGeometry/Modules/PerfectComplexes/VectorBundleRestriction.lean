/-
Copyright (c) 2026 Quillen K-Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Restriction
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction

/-!
# Degree-zero vector-bundle inclusion and open restriction

The comparison is the original single-complex/termwise restriction isomorphism.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- The degree-zero inclusion commutes with genuine termwise restriction. -/
def vectorBundleInclusionRestrictIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    vectorBundleInclusion X ⋙ strictRestrict j ≅
      AlgebraicGeometry.Scheme.Modules.vectorBundleRestrict j ⋙ vectorBundleInclusion U :=
  Functor.fullyFaithfulCancelRight (strictPerfect U).ι
    (Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X).ι
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.restrictFunctor j) (ComplexShape.up ℤ) 0))

end Quillen.PerfectComplexes

end

end
