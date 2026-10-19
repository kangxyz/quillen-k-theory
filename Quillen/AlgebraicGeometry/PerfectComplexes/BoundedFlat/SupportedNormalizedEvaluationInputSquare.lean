/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputSquare
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedNormalizedEvaluationInputRoutes
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteTargetNormalization
public import Quillen.Waldhausen.SmallModel.RouteRectangle

/-! # The actual supported evaluation square through four original normalizations

The geometric input square is transported through four specified target isomorphisms and
then the common-universe functors. Both complete evaluation routes and their strict original
supported reindex transport remain visible throughout.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation supportedPairReindexEvaluationIso

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
  {Np : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory ⥤
    (boundedFlatPerfectSupported A.obj.hom).FullSubcategory}
  {Na : (boundedFlatPerfectSupported A.obj.hom).FullSubcategory ⥤
    (boundedFlatPerfectSupported C.obj.hom).FullSubcategory}
  {Nb : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory ⥤
    (boundedFlatPerfectSupported D.obj.hom).FullSubcategory}
  {Nq : (boundedFlatPerfectSupported D.obj.hom).FullSubcategory ⥤
    (boundedFlatPerfectSupported C.obj.hom).FullSubcategory}
  (np : boundedFlatPerfectSupportedPullback p ≅ Np)
  (na : boundedFlatPerfectSupportedPullback a ≅ Na)
  (nb : boundedFlatPerfectSupportedPullback b ≅ Nb)
  (nq : boundedFlatPerfectSupportedPullback q ≅ Nq)

/-- Both actual supported evaluation routes retain the independently normalized raw square. -/
theorem supportedNormalizedInputSquare_hom :
    whiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom)
        (supportedNormalizedInputSquareIso p q a b h np na nb nq).hom ≫
        (isoSquareRoute (supportedNormalizedCoefficientIso b nb)
          (supportedNormalizedCoefficientIso q nq)).inv =
      (isoSquareRoute (supportedNormalizedCoefficientIso p np)
        (supportedNormalizedCoefficientIso a na)).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          supportedEvaluation (X := op C.obj.right) C.obj.hom)
          (supportedReindexInputSquare p q a b h)) := by
  unfold supportedNormalizedCoefficientIso
  rw [isoSquareRoute_targetNormalization, isoSquareRoute_targetNormalization]
  exact isoSquareTargetNormalization_rectangle
    (supportedEvaluationRouteIso a p).symm (supportedEvaluationRouteIso q b).symm
    (supportedPullbackInputSquareIso p q a b h) (supportedReindexInputSquare p q a b h)
    (isoWhiskerRight np (boundedFlatPerfectSupportedPullback a) ≪≫ isoWhiskerLeft Np na)
    (isoWhiskerRight nb (boundedFlatPerfectSupportedPullback q) ≪≫ isoWhiskerLeft Nb nq)
    (supportedEvaluationInputSquare_hom p q a b h)

/-- Original common-universe lifting retains the complete supported normalized rectangle. -/
theorem supportedSmallInputSquare_hom :
    whiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom ⋙ AsSmall.up.{u, u + 1, 0})
        (supportedSmallInputSquareIso p q a b h np na nb nq).hom ≫
        (isoSquareRoute (supportedSmallCoefficientIso b nb)
          (supportedSmallCoefficientIso q nq)).inv =
      (isoSquareRoute (supportedSmallCoefficientIso p np)
        (supportedSmallCoefficientIso a na)).inv ≫
        eqToHom (congrArg (fun F => F ⋙
          (supportedEvaluation (X := op C.obj.right) C.obj.hom ⋙ AsSmall.up.{u, u + 1, 0}))
          (supportedReindexInputSquare p q a b h)) :=
  smallModelRouteRectangle
    (supportedNormalizedCoefficientIso p np) (supportedNormalizedCoefficientIso a na)
    (supportedNormalizedCoefficientIso b nb) (supportedNormalizedCoefficientIso q nq)
    (supportedNormalizedInputSquareIso p q a b h np na nb nq)
    (supportedReindexInputSquare p q a b h)
    (supportedNormalizedInputSquare_hom p q a b h np na nb nq)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
