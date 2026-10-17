/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback

/-!
# Degree-zero vector-bundle inclusion and pullback

The actual single-complex inclusion commutes with arbitrary geometric pullback.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The actual degree-zero inclusion commutes with arbitrary pullback. -/
def vectorBundleInclusionPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    vectorBundleInclusion Y ⋙ strictPullback f ≅
      AlgebraicGeometry.Scheme.Modules.vectorBundlePullback f ⋙ vectorBundleInclusion X :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree Y).ι
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.pullback f) (ComplexShape.up ℤ) 0))

end Quillen.PerfectComplexes

end

end
