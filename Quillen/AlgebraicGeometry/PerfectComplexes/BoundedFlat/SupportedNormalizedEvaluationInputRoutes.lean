/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputRoutes
public import Quillen.Waldhausen.SmallModel.Whiskering

/-! # The actual supported normalized evaluation routes

The original geometric input square and each evaluation edge retain four independently
specified target normalizations and the actual common-universe functors. These routes are
defined before their input-rectangle coherence comparison.
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

/-- The actual geometric supported evaluation edge followed by its specified normalization. -/
def supportedNormalizedCoefficientIso {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    {N : (boundedFlatPerfectSupported B.obj.hom).FullSubcategory ⥤
      (boundedFlatPerfectSupported A.obj.hom).FullSubcategory}
    (n : boundedFlatPerfectSupportedPullback p ≅ N) :=
  (supportedPairReindexEvaluationIso p).symm ≪≫
    isoWhiskerLeft (supportedEvaluation (X := op B.obj.right) B.obj.hom) n

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

/-- Independently specified target normalizations around the original supported geometric square. -/
def supportedNormalizedInputSquareIso : Np ⋙ Na ≅ Nb ⋙ Nq :=
  (isoWhiskerRight np (boundedFlatPerfectSupportedPullback a) ≪≫ isoWhiskerLeft Np na).symm ≪≫
    supportedPullbackInputSquareIso p q a b h ≪≫
    (isoWhiskerRight nb (boundedFlatPerfectSupportedPullback q) ≪≫ isoWhiskerLeft Nb nq)

/-- The same actual supported normalized evaluation edge in the common universe. -/
def supportedSmallCoefficientIso {S T : Scheme.OpenPairs.{u}} (f : S ⟶ T)
    {N : (boundedFlatPerfectSupported T.obj.hom).FullSubcategory ⥤
      (boundedFlatPerfectSupported S.obj.hom).FullSubcategory}
    (n : boundedFlatPerfectSupportedPullback f ≅ N) :
    (supportedPairModelMap f).functor ⋙
        (supportedEvaluation (X := op S.obj.right) S.obj.hom ⋙ AsSmall.up.{u, u + 1, 0}) ≅
      (supportedEvaluation (X := op T.obj.right) T.obj.hom ⋙ AsSmall.up.{u, u + 1, 0}) ⋙
        smallModelFunctor N :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (supportedNormalizedCoefficientIso f n) AsSmall.up.{u, u + 1, 0}

/-- Lift the original independently normalized input square through the genuine up/down pair. -/
def supportedSmallInputSquareIso :
    smallModelFunctor Np ⋙ smallModelFunctor Na ≅
      smallModelFunctor Nb ⋙ smallModelFunctor Nq :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down.{u, u + 1, 0}
    (supportedNormalizedInputSquareIso p q a b h np na nb nq)) AsSmall.up.{u, u + 1, 0}

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
