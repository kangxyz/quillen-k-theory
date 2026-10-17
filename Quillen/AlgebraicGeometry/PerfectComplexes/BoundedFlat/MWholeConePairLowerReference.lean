/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLaurentPlacement
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassSharedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanMReference

/-! The actual polynomial lower anchor meets the original M bottom reference word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairLowerReference
open BassH0Merge BassReferenceMerge CommonReferenceNerve
private theorem precomp_cancel {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ B) (V : B ⥤ C) (J : C ⥤ D)
    {H : A ⥤ D} {T S : B ⥤ D} (e : H ≅ U ⋙ T)
    (a : T ≅ V ⋙ J) (b : T ≅ S) :
    (e ≪≫ isoWhiskerLeft U a) ≪≫ Functor.associator U V J ≪≫
      isoWhiskerLeft U (a.symm ≪≫ b) = e ≪≫ isoWhiskerLeft U b := by
  apply Iso.ext
  ext x
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.comp_obj, Iso.symm_hom,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The old sheet followed by its literal lower anchor is the original chart source node. -/
theorem chart_lower_reference (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (β.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    BassMOuterJoin.oldSideIso P p q β hc ≪≫
        Functor.associator (normalizedMap (polynomialProjection P a)).functor
          (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor
          (BassMWholeNerve.coefficientModel P (β.app c)).functor ≪≫
        isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
          (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q) =
      (BassOverlap.chartOverlapNodes P p q β hc 15).2 := by
  change (BassOverlap.commonToChartReference P p q β hc ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (BinaryNormalizationSimplex.total (coefficientMap P (β.app c))
          (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
            coefficientMap P ((polynomialUnderFunctor R).map p)))) ≪≫ _ ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        ((BinaryNormalizationSimplex.total (coefficientMap P (β.app c))
          (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
            coefficientMap P ((polynomialUnderFunctor R).map p))).symm ≪≫
              (BassOverlap.chartNodes P p q β 15).2) = _
  exact precomp_cancel (normalizedMap (polynomialProjection P a)).functor
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor
    (BassMWholeNerve.coefficientModel P (β.app c)).functor _ _ _

/-- The positive chart endpoint is the exact full bottom source word. -/
theorem plus_lower_word :
    referenceIso P p q ≪≫ BassMOuterJoin.oldSideIso P p q (underToLaurent R)
        (laurentPlus_projection P c) ≪≫
      Functor.associator (normalizedMap (polynomialProjection P a)).functor
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor
        (BassMWholeNerve.coefficientModel P ((underToLaurent R).app c)).functor ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P (underToLaurent R) p q) =
    InputLaurentProduct.pairAnchor P p q ≪≫
      isoWhiskerRight
        (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a))
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor ≪≫
      Functor.associator (normalizedMap (polynomialProjection P a)).functor
        (BassMWholeNerve.coefficientModel P ((underToLaurent R).app a)).functor
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor := by
  rw [chart_lower_reference]
  have h := congrArg (fun e ↦ referenceIso P p q ≪≫ e) (plus_source_reference P p q)
  change referenceIso P p q ≪≫ (BassOverlap.chartOverlapNodes P p q
    (underToLaurent R) (laurentPlus_projection P c) 15).2 = _ at h
  exact h.trans (by
    change referenceIso P p q ≪≫ (BassBottomCommonFamily.referenceIso P p q ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((BassProjectionPath.nodes P a 2).2.prod (Iso.refl _))) = _
    rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
    have he := eq_of_heq (Sigma.mk.inj (BassMJoin.plus_endpoint_node P (c := a))).2
    have hh := congrArg (fun e ↦ referenceIso P p q ≪≫
      BassBottomCommonFamily.referenceIso P p q ≪≫ isoWhiskerRight e
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor) he
    dsimp only [BassProjectionPath.nodes] at ⊢
    change (referenceIso P p q ≪≫ BassBottomCommonFamily.referenceIso P p q ≪≫
      isoWhiskerRight _ (CoefficientBassLaurentCompositionCarrier.reference P p q).functor) = _
    dsimp only [InputLaurentProduct.pairAnchor, laurentPlus, laurentMinus] at hh ⊢
    simp only [Iso.trans_assoc]
    exact hh)

/-- The inverse chart endpoint retains its separate exact projection equality transport. -/
theorem minus_lower_word :
    referenceIso P p q ≪≫ BassMOuterJoin.oldSideIso P p q (underToLaurentInvert R)
        (laurentMinus_projection P c) ≪≫
      Functor.associator (normalizedMap (polynomialProjection P a)).functor
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor
        (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app c)).functor ≪≫
      isoWhiskerLeft (normalizedMap (polynomialProjection P a)).functor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P
          (underToLaurentInvert R) p q) =
    InputLaurentProduct.pairAnchor P p q ≪≫
      isoWhiskerRight
        (BassMJoin.projectionEndpointIso P (underToLaurentInvert R) (laurentMinus_projection P a))
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor ≪≫
      Functor.associator (normalizedMap (polynomialProjection P a)).functor
        (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app a)).functor
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor := by
  rw [chart_lower_reference]
  have h := congrArg (fun e ↦ referenceIso P p q ≪≫ e) (minus_source_reference P p q)
  change referenceIso P p q ≪≫ (BassOverlap.chartOverlapNodes P p q
    (underToLaurentInvert R) (laurentMinus_projection P c) 15).2 = _ at h
  exact h.trans (by
    change referenceIso P p q ≪≫ (BassBottomCommonFamily.referenceIso P p q ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((BassProjectionPath.nodes P a 4).2.prod (Iso.refl _))) = _
    rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
    have he := eq_of_heq (Sigma.mk.inj (BassMJoin.minus_endpoint_node P (c := a))).2
    have hh := congrArg (fun e ↦ referenceIso P p q ≪≫
      BassBottomCommonFamily.referenceIso P p q ≪≫ isoWhiskerRight e
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor) he
    dsimp only [BassProjectionPath.nodes] at ⊢
    change (referenceIso P p q ≪≫ BassBottomCommonFamily.referenceIso P p q ≪≫
      isoWhiskerRight _ (CoefficientBassLaurentCompositionCarrier.reference P p q).functor) = _
    dsimp only [InputLaurentProduct.pairAnchor, laurentPlus, laurentMinus] at hh ⊢
    simp only [Iso.trans_assoc]
    exact hh)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairLowerReference
