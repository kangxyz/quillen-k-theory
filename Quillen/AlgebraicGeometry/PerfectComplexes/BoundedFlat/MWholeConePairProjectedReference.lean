/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairLowerReference

/-! The two original chart sheets keep their full projected binary reference. -/
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
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete original coefficient-to-polynomial side-row normalization. -/
def polynomialAnchor :
    (inputReference P p q ≫ normalizedMap (polynomialProjection P c)).functor ≅
      (normalizedMap (polynomialProjection P a) ≫
        CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor :=
  CoefficientBassSpanCompositionReference.squareAnchor P p q ≪≫
    BassMOuterJoin.movingSideBaseIso P p q

/-- The original projection square at the literal pair composite. -/
theorem polynomial_pair_naturality :
    polynomialProjection P c ≫ (coefficientMap P q ≫ coefficientMap P p) =
      (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
        coefficientMap P ((polynomialUnderFunctor R).map p)) ≫ polynomialProjection P a := by
  have h := (coefficientMap_naturality P (polynomialUnderCoefficient R) (p ≫ q)).symm
  simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.id_obj, coefficientMap_comp, polynomialProjection] using h

private theorem small_eq_chain {C D : Type u} [Category C] [Category D]
    {F G H K : C ⥤ D} (h₁ : F = G) (h₂ : G = H) (h₃ : F = H) (e : H ≅ K) :
    smallIso (eqToIso h₁) ≪≫ smallIso (eqToIso h₂ ≪≫ e) =
      smallIso (eqToIso h₃) ≪≫ smallIso e := by
  rw [← smallIso_trans, ← smallIso_trans, ← Iso.trans_assoc, eqToIso_trans]

/-- The original last-source and right-first routes retain their complete projection total. -/
theorem polynomial_anchor_normalized :
    polynomialAnchor P p q =
      (BinaryNormalizationSimplex.total (polynomialProjection P c)
        (coefficientMap P q ≫ coefficientMap P p)).symm ≪≫
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (polynomial_pair_naturality P p q))) ≪≫
      BinaryNormalizationSimplex.total
        (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
          coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a) := by
  apply congrArg ((BinaryNormalizationSimplex.total (polynomialProjection P c)
    (coefficientMap P q ≫ coefficientMap P p)).symm ≪≫ ·)
  exact small_eq_chain
    (congrArg boundedFlatNormalizedPullback
      (((DoubleSquareTrack.total_eq (coefficientMap P p) (coefficientMap P q)
        (coefficientMap P ((polynomialUnderFunctor R).map p))
        (coefficientMap P ((polynomialUnderFunctor R).map q))
        (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
        (coefficientMap_naturality P (polynomialUnderCoefficient R) p).symm
        (coefficientMap_naturality P (polynomialUnderCoefficient R) q).symm).symm).trans
          (Category.assoc (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a))))
    (congrArg boundedFlatNormalizedPullback
      (Category.assoc (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a)).symm)
    (congrArg boundedFlatNormalizedPullback (polynomial_pair_naturality P p q))
    (boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
        coefficientMap P ((polynomialUnderFunctor R).map p)) (polynomialProjection P a))

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (β.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The ordinary chart anchor includes its actual endpoint and polynomial projection route. -/
def chartAnchor : (BassProjectionPath.WholeReference.reference P c
    (inputReference P p q)).functor ≅
      ((normalizedMap (polynomialProjection P a) ≫
        CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) ≫
          BassMWholeNerve.coefficientModel P (β.app c)).functor :=
  isoWhiskerLeft (inputReference P p q).functor (BassMJoin.projectionEndpointIso P β hc) ≪≫
    isoWhiskerRight (polynomialAnchor P p q)
      (BassMWholeNerve.coefficientModel P (β.app c)).functor

private theorem side_anchor_of_corner
    (hcorner : BassMReferences.movingNodes P p q β hc 15 =
      BassOverlap.chartOverlapNodes P p q β hc 2) :
    BassMOuterJoin.movingSideIso P p q β hc = BassMOuterJoin.oldSideIso P p q β hc := by
  have he := (BassMOuterJoin.moving_side_row P p q β hc 0).symm.trans
    (hcorner.trans (BassMOuterJoin.old_side_row P p q β hc 0))
  have hs := eq_of_heq (Sigma.mk.inj he).2
  change BassMOuterJoin.movingSideIso P p q β hc ≪≫
    isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
        (BassMWholeNerve.coefficientModel P (β.app c)).functor) =
    BassMOuterJoin.oldSideIso P p q β hc ≪≫
      isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
        (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
          (BassMWholeNerve.coefficientModel P (β.app c)).functor) at hs
  have hh := congrArg (fun e ↦ e ≪≫
    (isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
      (isoWhiskerRight (BassMOuterJoin.sideBinaryNodes P p q 0).2
        (BassMWholeNerve.coefficientModel P (β.app c)).functor)).symm) hs
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hh

/-- The existing arbitrary-chart M anchor gives the complete projected moving reference. -/
theorem moving_chart_anchor :
    referenceIso P p q ≪≫ BassMOuterJoin.movingSideIso P p q β hc =
      chartAnchor P p q β hc := by
  change referenceIso P p q ≪≫ (BassMReferences.movingIso P p q β hc ≪≫
    isoWhiskerRight (BassMOuterJoin.movingSideBaseIso P p q)
      (BassMWholeNerve.coefficientModel P (β.app c)).functor) = _
  rw [← Iso.trans_assoc, CoefficientBassSpanCompositionReference.moving_chart_anchor]
  simp only [chartAnchor, polynomialAnchor, isoWhiskerRight_trans, Iso.trans_assoc]
  rfl

/-- The positive projected sheet is the unchanged original old chart sheet. -/
theorem plus_chart_anchor :
    chartAnchor P p q (underToLaurent R) (laurentPlus_projection P c) =
      referenceIso P p q ≪≫ BassMOuterJoin.oldSideIso P p q (underToLaurent R)
        (laurentPlus_projection P c) := by
  rw [← moving_chart_anchor, side_anchor_of_corner P p q (underToLaurent R)
    (laurentPlus_projection P c) (BassMOuterJoin.plus_side_corner P p q)]

/-- The inverse projected sheet uses its separate complete original old chart anchor. -/
theorem minus_chart_anchor :
    chartAnchor P p q (underToLaurentInvert R) (laurentMinus_projection P c) =
      referenceIso P p q ≪≫ BassMOuterJoin.oldSideIso P p q (underToLaurentInvert R)
        (laurentMinus_projection P c) := by
  rw [← moving_chart_anchor, side_anchor_of_corner P p q (underToLaurentInvert R)
    (laurentMinus_projection P c) (BassMOuterJoin.minus_side_corner P p q)]

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairLowerReference
