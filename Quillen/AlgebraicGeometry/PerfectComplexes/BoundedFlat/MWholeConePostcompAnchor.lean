/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePostcompCap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePostcompReferenceWord
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeTripleLaurentAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetLaurentNormalization

/-! The ordinary postcomposition cap retains the frozen original whole Laurent anchor. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
open BassH0Merge BassReferenceMerge BassProjectionPath.WholeReference
attribute [local irreducible] boundedFlatNormalizedPullback
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "k" => coefficientMap P w
local notation "j" => coefficientMap P q ≫ coefficientMap P p
local notation "l" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) w)
local notation "t" => laurentPlus P d ≫ polynomialProjection P d
local notation "s" => laurentPlus P c ≫ polynomialProjection P c
local notation "r" => laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p
local notation "W" =>
  coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) ((p ≫ q) ≫ w)) ≫
    laurentProjection P a
local notation "E" => inputReference P p q
local notation "G" => BassOverlap.commonReference P p q

private theorem inputIso_small : inputIso P p q w =
    smallIso (boundedFlatNormalizedPullbackCompIso k j) := by
  change NormalizedTripleSimplex.leftFirst k (coefficientMap P q) (coefficientMap P p) ≪≫
    Iso.refl _ = _
  rw [Iso.trans_refl]
  rfl

private theorem projectionIso_small :
    CoefficientBassSeedTargetReferenceTransport.projectionIso P w =
      smallIso ((boundedFlatNormalizedPullbackCompIso t k).symm ≪≫
        eqToIso (congrArg boundedFlatNormalizedPullback
          (CoefficientBassSeedTargetReferenceTransport.projection_square P w)) ≪≫
        boundedFlatNormalizedPullbackCompIso l s) := by
  unfold CoefficientBassSeedTargetReferenceTransport.projectionIso
  simp only [smallIso_trans, smallIso_eqToIso]
  rfl

private theorem oldReference_small : BassMWholeConeCarrier.referenceIso P p q =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassMReferences.middle_total P p q).symm) ≪≫
        boundedFlatNormalizedPullbackCompIso s j).symm := by
  have h : BassMWholeConeCarrier.referenceIso P p q =
      (BassMReferences.middleIso P p q).symm := by
    unfold BassMWholeConeCarrier.referenceIso
      CoefficientBassSeedCarrierLaurentReference.referenceIso BassMReferences.middleIso
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  rw [h]
  rfl

private theorem target_reference_small :
    CoefficientBassSeedTargetReferenceTransport.referenceIso P w E G
      (BassMWholeConeCarrier.referenceIso P p q) =
    smallIso
      (isoWhiskerLeft (boundedFlatNormalizedPullback j)
        ((boundedFlatNormalizedPullbackCompIso t k).symm ≪≫
          eqToIso (congrArg boundedFlatNormalizedPullback
            (CoefficientBassSeedTargetReferenceTransport.projection_square P w)) ≪≫
          boundedFlatNormalizedPullbackCompIso l s) ≪≫
      isoWhiskerRight
        (eqToIso (congrArg boundedFlatNormalizedPullback
          (BassMReferences.middle_total P p q).symm) ≪≫
            boundedFlatNormalizedPullbackCompIso s j).symm
        (boundedFlatNormalizedPullback l)) := by
  change Iso.refl _ ≪≫ isoWhiskerLeft (E).functor
    (CoefficientBassSeedTargetReferenceTransport.projectionIso P w) ≪≫
      Iso.refl _ ≪≫ isoWhiskerRight (BassMWholeConeCarrier.referenceIso P p q)
        (BassH0Merge.normalizedMap l).functor = _
  simp only [Iso.refl_trans]
  rw [projectionIso_small, oldReference_small]
  change isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback j ⋙ AsSmall.up)
      (smallIso ((boundedFlatNormalizedPullbackCompIso t k).symm ≪≫
        eqToIso (congrArg boundedFlatNormalizedPullback
          (CoefficientBassSeedTargetReferenceTransport.projection_square P w)) ≪≫
        boundedFlatNormalizedPullbackCompIso l s)) ≪≫
      isoWhiskerRight
        (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
          (BassMReferences.middle_total P p q).symm) ≪≫
          boundedFlatNormalizedPullbackCompIso s j).symm)
        (AsSmall.down ⋙ boundedFlatNormalizedPullback l ⋙ AsSmall.up) = _
  rw [smallIso_precomp, smallIso_postcomp, ← smallIso_trans]

/-- Full isomorphism equality with the unchanged frozen target-whiskered M reference. -/
theorem anchor_join :
    (TripleLaurent.anchor P p q w ≪≫
      isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor) ≪≫
      CoefficientBassSeedTargetReferenceTransport.referenceIso P w E G
        (BassMWholeConeCarrier.referenceIso P p q) =
    BassMWholeNerve.postcompAnchor P p q w := by
  rw [inputIso_small, target_reference_small]
  have hi : isoWhiskerRight (smallIso (boundedFlatNormalizedPullbackCompIso k j))
      (BassProjectionPath.source P d).functor =
      smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso k j)
        (boundedFlatNormalizedPullback t)) :=
    smallIso_postcomp (boundedFlatNormalizedPullbackCompIso k j)
      (boundedFlatNormalizedPullback t)
  rw [hi]
  have hl : W = (t ≫ k) ≫ j :=
    (TripleLaurent.total P p q w).trans (Category.assoc t k j).symm
  have h := postcomp_projection_word t k j l s r W
    (CoefficientBassSeedTargetReferenceTransport.projection_square P w)
    (BassMReferences.middle_total P p q).symm hl (TripleLaurent.total P p q w)
    (BassMWholeNerve.postcomp_total P p q w)
  change (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (TripleLaurent.total P p q w)) ≪≫ boundedFlatNormalizedPullbackCompIso t (k ≫ j)) ≪≫
      smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso k j)
        (boundedFlatNormalizedPullback t))) ≪≫
      smallIso
        (isoWhiskerLeft (boundedFlatNormalizedPullback j)
          ((boundedFlatNormalizedPullbackCompIso t k).symm ≪≫
            eqToIso (congrArg boundedFlatNormalizedPullback
              (CoefficientBassSeedTargetReferenceTransport.projection_square P w)) ≪≫
            boundedFlatNormalizedPullbackCompIso l s) ≪≫
          isoWhiskerRight
            (eqToIso (congrArg boundedFlatNormalizedPullback
              (BassMReferences.middle_total P p q).symm) ≪≫
              boundedFlatNormalizedPullbackCompIso s j).symm
            (boundedFlatNormalizedPullback l)) =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (BassMWholeNerve.postcomp_total P p q w)) ≪≫ boundedFlatNormalizedPullbackCompIso l r)
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso h

/-- The literal cone-map route retains the original H0 source and target anchors as well. -/
theorem actual_anchor_join :
    (((TripleLaurent.anchor P p q w ≪≫
        isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor) ≪≫
      (FourEdge.Target.terminalBoundaryAnchor P w E).symm) ≪≫
      FourEdge.Target.sourceBoundaryAnchor P w E) ≪≫
      isoWhiskerRight (BassMWholeConeCarrier.referenceIso P p q)
        (FourEdge.Target.sourcePost P w).functor =
    BassMWholeNerve.postcompAnchor P p q w := by
  calc
    _ = (TripleLaurent.anchor P p q w ≪≫
        isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor) ≪≫
      (((FourEdge.Target.terminalBoundaryAnchor P w E).symm ≪≫
        FourEdge.Target.sourceBoundaryAnchor P w E) ≪≫
        isoWhiskerRight (BassMWholeConeCarrier.referenceIso P p q)
          (FourEdge.Target.sourcePost P w).functor) := by simp only [Iso.trans_assoc]
    _ = _ := (congrArg (fun e ↦ (TripleLaurent.anchor P p q w ≪≫
        isoWhiskerRight (inputIso P p q w) (BassProjectionPath.source P d).functor) ≪≫ e)
      (FourEdge.TargetCone.source_action_anchor P w E G
        (BassMWholeConeCarrier.referenceIso P p q))).trans (anchor_join P p q w)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.Postcomp
