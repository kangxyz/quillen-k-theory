/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionFirstNormalNode
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductPolynomialRows

/-! Full central reference identity on both product/middle H1 joins. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

def middleChartCenter : BassOverlap.Node P u v :=
  BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b),
      eqToIso (chartFirstSourceEq P v α hb) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)⟩ : BassH0Diagram.Node P v)

def productChartCenter : BassOverlap.Node P u v :=
  ⟨(CoefficientSquareFamilies.polynomialNodes P u 4).1 ≫
    CoefficientSquareFamilies.chartSource P v α,
    chartIso P u v α hb ≪≫ isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u 4).2
      (CoefficientSquareFamilies.chartSource P v α).functor⟩

theorem middle_chart_center_original :
    BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb 9) = middleChartCenter P u v α hb :=
  congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v)) (chart_first_normal P v α hb)

/-- The product center retains its actual original polynomial-square target reference. -/
theorem product_chart_center_original :
    BassH1References.chartNodes P u v α hb 20 = productChartCenter P u v α hb := by
  change BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (4, 0)) = _
  unfold BassH1References.chartNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  have hf : ((CoefficientSquareFamilies.polynomialNodes P u 4).1 ≫
      (CoefficientSquareFamilies.chartNodes P v α 0).1).functor =
      (productChartCenter P u v α hb).1.functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change chartIso P u v α hb ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((CoefficientSquareFamilies.polynomialNodes P u 4).2.prod
        (Iso.refl (CoefficientSquareFamilies.chartSource P v α).functor)) = _
  have hi := composition_pair_iso (CoefficientSquareFamilies.polynomialNodes P u 4).2
    (Iso.refl (CoefficientSquareFamilies.chartSource P v α).functor)
  simp only [isoWhiskerLeft_refl, Iso.trans_refl] at hi
  exact congrArg (fun ν ↦ chartIso P u v α hb ≪≫ ν) hi

theorem chart_center_functor : (middleChartCenter P u v α hb).1.functor =
    (productChartCenter P u v α hb).1.functor := rfl

/-- The original row centers agree by canonical normalized three-factor associativity. -/
theorem chart_center_reference : (middleChartCenter P u v α hb).2 =
    (productChartCenter P u v α hb).2 := by
  have hm : eqToIso (chartFirstSourceEq P v α hb) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartFirstGeom P v α hb)) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  have hp : (CoefficientSquareFamilies.polynomialNodes P u 4).2 =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)) ≪≫
      boundedFlatNormalizedPullbackCompIso (polynomialProjection P b) (coefficientMap P u)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change middleIso P u v ≪≫ isoWhiskerLeft (BassH1Components.coefficientMapModel P u).functor
      (eqToIso (chartFirstSourceEq P v α hb) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (polynomialProjection P b)) =
    chartIso P u v α hb ≪≫ isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u 4).2
      (CoefficientSquareFamilies.chartSource P v α).functor
  rw [hm, hp]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (middle_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
        (coefficientMap P u)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback (coefficientMap P u) ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartFirstGeom P v α hb)) ≪≫
        boundedFlatNormalizedPullbackCompIso
          (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
          (polynomialProjection P b))) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_total P u v α hb).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) ≪≫
    isoWhiskerRight (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)) ≪≫
      boundedFlatNormalizedPullbackCompIso (polynomialProjection P b) (coefficientMap P u)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ⋙
          AsSmall.up)
  rw [smallIso_precomp, smallIso_postcomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (polynomialProjection P b) (coefficientMap P u)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (chartFirstGeom P v α hb)
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
      (middle_total P u v).symm (chart_total P u v α hb).symm)

/-- Both original full central nodes agree, with every normalization and equality iso retained. -/
theorem middle_product_chart_center :
    BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (middleIso P u v)
      (BassH0Diagram.chartNodes P v α hb 9) = BassH1References.chartNodes P u v α hb 20 := by
  rw [middle_chart_center_original, product_chart_center_original]
  apply Sigma.ext (Model.Hom.ext (chart_center_functor P u v α hb))
  exact heq_of_eq (chart_center_reference P u v α hb)

theorem plus_row_center : BassH1References.middleNodes P u v 9 =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 20 :=
  middle_product_chart_center P u v (underToLaurent R) (laurentPlus_projection P b)

theorem minus_row_center : BassH1References.middleNodes P u v 20 =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 20 :=
  middle_product_chart_center P u v (underToLaurentInvert R) (laurentMinus_projection P b)

end Quillen.PerfectComplexes.BassH1Join
