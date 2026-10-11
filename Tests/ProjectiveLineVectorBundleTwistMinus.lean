/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.VectorBundleTwistMinus

/-! # Original-map consumers of exact negative-twisted pullback -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace Quillen.Tests.ProjectiveLineVectorBundleTwistMinus

/-- Forgetting the output keeps the actual kernel of the original pulled-back module sheaf. -/
theorem original_object (R : CommRingCat.{u}) (E : FiniteLocallyFree (Spec R)) :
    ((vectorBundleTwistedPullback R).toFunctor.obj E).obj =
      twistMinus R ((Scheme.Modules.pullback (projection R)).obj E.obj) := rfl

/-- The induced bundle arrow retains the literal square of the original geometric pullback map. -/
theorem original_morphism_square (R : CommRingCat.{u})
    {E F : FiniteLocallyFree (Spec R)} (f : E ⟶ F) :
    (finiteLocallyFree (twoChartLine R)).ι.map
        ((vectorBundleTwistedPullback R).toFunctor.map f) ≫
      twistMinusInclusion R ((Scheme.Modules.pullback (projection R)).obj F.obj) =
    twistMinusInclusion R ((Scheme.Modules.pullback (projection R)).obj E.obj) ≫
      prod.map ((Scheme.Modules.pullback (projection R)).map f.hom)
        ((Scheme.Modules.pullback (projection R)).map f.hom) :=
  twistMinusMap_inclusion R _

/-- Every original vector-bundle conflation maps to an actual short exact module-sheaf sequence. -/
theorem original_conflation (R : CommRingCat.{u})
    (S : ShortComplex (FiniteLocallyFree (Spec R)))
    (hS : (vectorBundleExactStructure (Spec R)).conflation S) :
    ((S.map (vectorBundleTwistedPullback R).toFunctor).map
      (finiteLocallyFree (twoChartLine R)).ι).ShortExact :=
  (vectorBundleTwistedPullback R).map_conflation S hS

/-- The public K-map is induced by precisely the original exact twisted-pullback functor. -/
theorem original_k_map (R : CommRingCat.{u}) (n : ℕ) (x : SchemeK (Spec R) n) :
    twistedPullbackKMap R n x =
      (vectorBundleTwistedPullback R).smallKMap n x := rfl

end Quillen.Tests.ProjectiveLineVectorBundleTwistMinus
