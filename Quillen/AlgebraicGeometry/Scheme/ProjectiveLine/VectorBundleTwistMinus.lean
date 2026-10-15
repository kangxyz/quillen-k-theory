/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TwistMinusFunctor
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Pullback

/-!
# Negative-twisted pullback on genuine vector bundles

The canonical negative twist lifts to the inherited vector-bundle exact structure.
Composing with the original projection pullback gives an exact functor and its induced
K-group map. Its underlying module-sheaf functor is literally pullback followed by the
checked kernel twist. No projective-bundle equivalence is asserted here.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules
variable (R : CommRingCat.{u})

/-- The canonical negative twist on actual finite locally free module sheaves. -/
def vectorBundleTwistMinus : FiniteLocallyFree (twoChartLine R) ⥤
    FiniteLocallyFree (twoChartLine R) :=
  (finiteLocallyFree (twoChartLine R)).lift
    ((finiteLocallyFree (twoChartLine R)).ι ⋙ twistMinusFunctor R)
    (fun M => twistMinus_finiteLocallyFree R M.obj)

lemma vectorBundleTwistMinus_comp_forget :
    vectorBundleTwistMinus R ⋙ (finiteLocallyFree (twoChartLine R)).ι =
      (finiteLocallyFree (twoChartLine R)).ι ⋙ twistMinusFunctor R := rfl

instance vectorBundleTwistMinus_additive : (vectorBundleTwistMinus R).Additive := by
  dsimp [vectorBundleTwistMinus]
  infer_instance

/-- The negative twist as an exact functor for inherited vector-bundle structures. -/
def vectorBundleTwistMinusExact : ExactFunctor (vectorBundleExactStructure (twoChartLine R))
    (vectorBundleExactStructure (twoChartLine R)) where
  toFunctor := vectorBundleTwistMinus R
  map_conflation S hS := by
    change ((S.map (finiteLocallyFree (twoChartLine R)).ι).map (twistMinusFunctor R)).ShortExact
    exact twistMinusFunctor_shortExact R _ hS

/-- Original geometric projection pullback followed by the exact negative twist. -/
def vectorBundleTwistedPullback : ExactFunctor (vectorBundleExactStructure (Spec R))
    (vectorBundleExactStructure (twoChartLine R)) :=
  (vectorBundleExactPullback (projection R)).comp (vectorBundleTwistMinusExact R)

lemma vectorBundleTwistedPullback_comp_forget :
    (vectorBundleTwistedPullback R).toFunctor ⋙ (finiteLocallyFree (twoChartLine R)).ι =
      (finiteLocallyFree (Spec R)).ι ⋙ Scheme.Modules.pullback (projection R) ⋙
        twistMinusFunctor R := rfl
/-- The induced negative-twisted pullback map on the original vector-bundle K-groups. -/
def twistedPullbackKMap (n : ℕ) : SchemeK (Spec R) n →* SchemeK (twoChartLine R) n :=
  (vectorBundleTwistedPullback R).smallKMap n

end AlgebraicGeometry.Scheme.ProjectiveLine
