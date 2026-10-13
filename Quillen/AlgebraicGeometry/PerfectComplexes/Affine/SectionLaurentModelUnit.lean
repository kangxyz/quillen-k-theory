/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentEvaluationUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelIntertwining

/-!
# Original Laurent evaluation after normalization and universe lifting

The original categorical unit square survives the actual chosen-zero normalization and AsSmall
lift. Opaque component identities retain the literal source action, original target conjugation
and unchanged evaluation comparison before their whole-prespectrum realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The unchanged normalized geometric Laurent action in the original common-universe model. -/
def boundedFlatAffineOriginalLaurentModelUnit (R : CommRingCat.{u}) :
    (boundedFlatAffineOriginalCoefficientModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).functor ⟶
      (boundedFlatAffineOriginalCoefficientModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).functor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation
      (boundedFlatPerfectPullback_exact (laurentProjection R))
      (boundedFlatPerfectPullback_exact (laurentProjection R))
      (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom)
    AsSmall.up)

/-- The unchanged strict section action at the exact original Model functor endpoint. -/
def boundedFlatAffineSectionLaurentModelUnit (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).functor ⟶
    (boundedFlatAffineSectionModelMap (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).functor :=
  (boundedFlatAffineSectionLaurentPullbackUnitIso R).hom

/-- The original comparison component is the raw section transition followed by normalization. -/
theorem boundedFlatAffineSectionLaurentEvaluationCoefficientIso_hom_app
    (R : CommRingCat.{u}) (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineSectionEvaluationCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).hom.app s =
    (AsSmall.up : BoundedFlatPerfect (Spec (.of (LaurentPolynomial R))) ⥤
      SmallModel (BoundedFlatPerfect (Spec (.of (LaurentPolynomial R))))).map
      ((boundedFlatAffineSectionCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
        (laurentCoefficient R)).hom.app s ≫
        (boundedFlatPullbackNormalizationIso (laurentProjection R)).hom.app
          ((boundedFlatAffineOriginalEvaluation R).obj s)) := by
  rw [boundedFlatAffineSectionEvaluationCoefficientIso_hom_app]
  simp only [Quillen.CategoryTheory.GrothendieckSections.normalizedCoefficientIso,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    ← boundedFlatAffineSectionCoefficientIso_eq]
  rfl

/-- The actual Laurent evaluation comparison intertwines both original Model actions. -/
theorem boundedFlatAffineSectionLaurentModelEvaluationUnitSquare (R : CommRingCat.{u}) :
    whiskerRight (boundedFlatAffineSectionLaurentModelUnit R)
        (boundedFlatAffineSectionEvaluationModelMap (.of (LaurentPolynomial R))).functor ≫
      (boundedFlatAffineSectionEvaluationCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
        (laurentCoefficient R)).hom =
    (boundedFlatAffineSectionEvaluationCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
        (laurentCoefficient R)).hom ≫
      whiskerLeft (boundedFlatAffineSectionEvaluationModelMap R).functor
        (boundedFlatAffineOriginalLaurentModelUnit R) :=
  boundedFlatAffineSectionModelEvaluation_intertwine
    (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R)
    (boundedFlatAffineSectionLaurentModelUnit R)
    (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom
    (boundedFlatAffineSectionLaurentCoefficientUnitSquare R)

end Quillen.PerfectComplexes
