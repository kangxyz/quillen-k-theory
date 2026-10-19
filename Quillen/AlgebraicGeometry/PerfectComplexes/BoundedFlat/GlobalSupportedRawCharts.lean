/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawGeometry
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationModelNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackForgetIso

/-!
# Original normalized supported Bass chart edges

The four raw Model arrows are the existing supported geometric pullbacks on the actual
integer-base open pairs. The two triangles use the original supported composition isomorphism,
the actual pair equality, and precisely the existing chosen-zero normalizations. Evaluation
retains its original comparison isomorphisms. These are chart edges and whole categorical
triangles, not a constructed supported raw cone, seed or localization-null comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass
open SupportedTensorEvaluation GlobalSectionChangeIndex

/-- The original geometric supported Model attached to an actual open pair. -/
abbrev rawModel (A : Scheme.OpenPairs.{u}) : Model.{u+1} :=
  modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)

/-- The actual polynomial projection, with the existing geometric zero normalization. -/
abbrev projectionMap (A : Scheme.QuasiCompactOpenPairs.{u}) :
    rawModel A.obj ⟶ rawModel (Geometry.polynomial A) :=
  evaluationRawMap (Geometry.projection A)

/-- The actual Laurent projection, with the existing geometric zero normalization. -/
abbrev laurentProjectionMap (A : Scheme.QuasiCompactOpenPairs.{u}) :
    rawModel A.obj ⟶ rawModel (Geometry.laurent A) :=
  evaluationRawMap (Geometry.laurentProjection A)

/-- The original normalized positive supported chart. -/
abbrev plusMap (A : Scheme.QuasiCompactOpenPairs.{u}) :
    rawModel (Geometry.polynomial A) ⟶ rawModel (Geometry.laurent A) :=
  evaluationRawMap (Geometry.plus A)

/-- The original normalized inverse-coordinate supported chart. -/
abbrev minusMap (A : Scheme.QuasiCompactOpenPairs.{u}) :
    rawModel (Geometry.polynomial A) ⟶ rawModel (Geometry.laurent A) :=
  evaluationRawMap (Geometry.minus A)

/-- The positive triangle is the original supported composition, with its actual pair equality. -/
def plusPullbackIso (A : Scheme.QuasiCompactOpenPairs.{u}) :
    boundedFlatPerfectSupportedPullback (Geometry.laurentProjection A) ≅
      boundedFlatPerfectSupportedPullback (Geometry.projection A) ⋙
        boundedFlatPerfectSupportedPullback (Geometry.plus A) :=
  eqToIso (congrArg boundedFlatPerfectSupportedPullback (Geometry.plus_projection A)).symm ≪≫
    boundedFlatPerfectSupportedPullbackCompIso (Geometry.plus A) (Geometry.projection A)

/-- The inverse chart retains its own original supported composition isomorphism. -/
def minusPullbackIso (A : Scheme.QuasiCompactOpenPairs.{u}) :
    boundedFlatPerfectSupportedPullback (Geometry.laurentProjection A) ≅
      boundedFlatPerfectSupportedPullback (Geometry.projection A) ⋙
        boundedFlatPerfectSupportedPullback (Geometry.minus A) :=
  eqToIso (congrArg boundedFlatPerfectSupportedPullback (Geometry.minus_projection A)).symm ≪≫
    boundedFlatPerfectSupportedPullbackCompIso (Geometry.minus A) (Geometry.projection A)

/-- Transport a geometric supported triangle through the three existing raw normalizations. -/
def chartNormalizationIso {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C)
    (i : boundedFlatPerfectSupportedPullback r ≅
      boundedFlatPerfectSupportedPullback q ⋙ boundedFlatPerfectSupportedPullback p) :
    (evaluationRawMap r).functor ≅ (evaluationRawMap q ≫ evaluationRawMap p).functor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down
    ((evaluationRawNormalization r).symm ≪≫ i ≪≫
      isoWhiskerRight (evaluationRawNormalization q) (boundedFlatPerfectSupportedPullback p) ≪≫
      isoWhiskerLeft _ (evaluationRawNormalization p))) AsSmall.up

/-- All original positive-chart normalizations remain in the whole raw Model triangle. -/
def plusCompositionIso (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (laurentProjectionMap A).functor ≅ (projectionMap A ≫ plusMap A).functor :=
  chartNormalizationIso _ _ _ (plusPullbackIso A)

/-- All original inverse-chart normalizations remain in its independent raw Model triangle. -/
def minusCompositionIso (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (laurentProjectionMap A).functor ≅ (projectionMap A ≫ minusMap A).functor :=
  chartNormalizationIso _ _ _ (minusPullbackIso A)

/-- The polynomial evaluation edge is the existing entire supported evaluation comparison. -/
def projectionEvaluationIso (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  evaluationComparisonIso (Geometry.projection A)

/-- The Laurent evaluation edge uses the same original supported comparison. -/
def laurentProjectionEvaluationIso (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  evaluationComparisonIso (Geometry.laurentProjection A)

/-- The positive evaluation edge retains both specified selected-zero normalizations. -/
def plusEvaluationIso (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  evaluationComparisonIso (Geometry.plus A)

/-- The inverse-coordinate evaluation edge retains the same specified normalizations. -/
def minusEvaluationIso (A : Scheme.QuasiCompactOpenPairs.{u}) :=
  evaluationComparisonIso (Geometry.minus A)

private theorem pullbackTriangle_forget {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C) (h : p ≫ q = r) :
    isoWhiskerRight
        (eqToIso (congrArg boundedFlatPerfectSupportedPullback h).symm ≪≫
          boundedFlatPerfectSupportedPullbackCompIso p q)
        (tensorCoefficientSupportedForget A.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget C.obj.hom)
        (eqToIso (congrArg (fun k : A ⟶ C => boundedFlatPerfectPullback k.hom.right) h).symm ≪≫
          boundedFlatPerfectPullbackCompIso p.hom.right q.hom.right) := by
  rw [isoWhiskerRight_trans, supportedPullbackEquality_forget_iso h.symm,
    boundedFlatPerfectSupportedPullbackCompIso_forget, isoWhiskerLeft_trans]

/-- The whole positive triangle, including equality transport, has the original ambient image. -/
theorem plusPullbackIso_forget (A : Scheme.QuasiCompactOpenPairs.{u}) :
    isoWhiskerRight (plusPullbackIso A)
        (tensorCoefficientSupportedForget (Geometry.laurent A).obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget A.obj.obj.hom)
        (eqToIso (congrArg
          (fun k : Geometry.laurent A ⟶ A.obj => boundedFlatPerfectPullback k.hom.right)
          (Geometry.plus_projection A)).symm ≪≫
        boundedFlatPerfectPullbackCompIso (Geometry.plus A).hom.right
          (Geometry.projection A).hom.right) :=
  pullbackTriangle_forget _ _ _ (Geometry.plus_projection A)

/-- The independent inverse triangle retains its entire original ambient comparison. -/
theorem minusPullbackIso_forget (A : Scheme.QuasiCompactOpenPairs.{u}) :
    isoWhiskerRight (minusPullbackIso A)
        (tensorCoefficientSupportedForget (Geometry.laurent A).obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget A.obj.obj.hom)
        (eqToIso (congrArg
          (fun k : Geometry.laurent A ⟶ A.obj => boundedFlatPerfectPullback k.hom.right)
          (Geometry.minus_projection A)).symm ≪≫
        boundedFlatPerfectPullbackCompIso (Geometry.minus A).hom.right
          (Geometry.projection A).hom.right) :=
  pullbackTriangle_forget _ _ _ (Geometry.minus_projection A)

end Quillen.PerfectComplexes.GlobalSupportedRawBass
