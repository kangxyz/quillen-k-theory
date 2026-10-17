/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompInputFirstCell
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ReferenceWhiskeringFamily

/-! The actual second chart cell of the final postcomposition and input-cap seam. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputSecondCell
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialTripleAnchor BassH0Merge BassH1Join
open CoefficientBassRaw1PolynomialPostcompInputFirstCell
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- Every original second chart node is retained under actual postcomposition. -/
def postcompSecondNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (postcompLowerIso P β p q w)
    (postcompNode (normalizedMap (laurentArrow P w))
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β p q i))

/-- The input cap's second row keeps its actual polynomial precomposition and placement. -/
def inputSecondNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β p q w)
    (precompNode (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β q w i))

private theorem pair_first_two :
    CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β p q 2 =
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
      (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
        (CoefficientBassLaurentCompositionCarrier.nodes P p q 2)) := by
  exact (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes P β p q 2).symm.trans
    (CoefficientBassRaw1PolynomialLowerAttachment.sheet_target_nodes P β p q 2)

private theorem postcomp_seam :
    postcompFirstNodes P β p q w 4 = postcompSecondNodes P β p q w 2 := by
  have h : CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β p q 4 =
      CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β p q 2 :=
    (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes P β p q 4).symm.trans
      (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes P β p q 2)
  dsimp only [postcompFirstNodes, postcompSecondNodes]
  rw [h]

private theorem input_seam :
    inputFirstNodes P β p q w 4 = inputSecondNodes P β p q w 2 := by
  rw [inputSecondNodes, pair_first_two]
  change CommonReferenceProduct.reanchor (inputLowerIso P β p q w)
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm
      (CoefficientBassRaw1ChartCompositionProduct.terminalNodes P β p q w 2)) = _
  rw [CoefficientBassRaw1ChartCompositionProduct.terminal_node]
  simp only [CommonReferenceProduct.reanchor, Iso.symm_self_id_assoc]

private theorem common_node :
    postcompSecondNodes P β p q w 2 = inputSecondNodes P β p q w 2 :=
  (postcomp_seam P β p q w).symm.trans
    ((first_nodes P β p q w 4).trans (input_seam P β p q w))

/-- The complete second chart rows agree with both fixed whiskerings and full references. -/
theorem second_nodes (i : Fin 5) :
    postcompSecondNodes P β p q w i = inputSecondNodes P β p q w i := by
  apply prePost_families_match
    (polynomialReference P p q w ≫ normalizedMap (chart P β d))
    (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p)
    (normalizedMap (laurentArrow P w))
    (CoefficientBassRaw1ChartCompositionProduct.chartReference P β q)
    (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β q)
    (ρ := postcompLowerIso P β p q w ≪≫
      isoWhiskerRight
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q ≪≫
          CoefficientMovingSquareRows.secondAnchor
            (coefficientMap P ((polynomialUnderFunctor R).map p))
            (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((laurentUnderFunctor R).map q))
            (coefficientMap P (β.app b)) (coefficientMap P (β.app c))
            (coefficientMap_naturality P β q).symm)
        (normalizedMap (laurentArrow P w)).functor)
    («σ» := inputLowerIso P β p q w ≪≫
      isoWhiskerLeft (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p).functor
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β q w ≪≫
          CoefficientMovingSquareRows.firstAnchor
            (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((polynomialUnderFunctor R).map w))
            (coefficientMap P ((laurentUnderFunctor R).map q))
            (coefficientMap P ((laurentUnderFunctor R).map w))
            (coefficientMap P (β.app b)) (coefficientMap P (β.app c))
            (coefficientMap P (β.app d))
            (coefficientMap_naturality P β q).symm
            (coefficientMap_naturality P β w).symm))
    ?_ ?_ 2 (common_node P β p q w) i
  · intro j
    simp only [postcompSecondNodes,
      CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
      CommonReferenceProduct.reanchor, postcompNode, preReferenceNode, prePostNodes,
      isoWhiskerRight_trans, whisker_iso_interchange, Iso.trans_assoc]
    rfl
  · intro j
    simp only [inputSecondNodes,
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes,
      CommonReferenceProduct.reanchor, precompNode, postReferenceNode, prePostNodes,
      isoWhiskerLeft_trans, Iso.trans_assoc]

/-- The whole second chart row keeps the unchanged original square parameter. -/
theorem second_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P β p q w))
      (mapParameter (postcompNode (normalizedMap (laurentArrow P w)))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
          (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β p q)
          (NativeSquareFiveSimplex.parameter t))) =
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β p q w))
      (mapParameter (precompNode (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β q w)
          (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β q w)
          (NativeSquareFiveSimplex.parameter t))) := by
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter]
  exact congrArg (fun N ↦ parameter
    (polynomialReference P p q w ≫ normalizedMap (chart P β d)) N
    (NativeSquareFiveSimplex.parameter t)) (funext (second_nodes P β p q w))

/-- Actual source precomposition and placement keep the complete Laurent nerve. -/
theorem input_precomp_laurent
    (y : |parameterSSet (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β q w)|) :
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
        (CoefficientBassRaw1PolynomialPairCone.laurent P β q w y)) =
    SSet.toTop.map (left₀ (polynomialReference P p q w)
      (BassMWholeNerve.coefficientModel P (β.app d))
      (polynomialReference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d)) (Iso.refl _))
      (mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β p q w))
        (mapParameter (precompNode
          (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p)) y)) := by
  have h := ConcreteCategory.congr_hom (CutOpenPrecomp.firstMap_left
    (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
    (BassMWholeNerve.coefficientModel P (β.app d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β q w) (Iso.refl _)) y
  change CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
    (CoefficientBassRaw1PolynomialPairCone.laurent P β q w y) =
    CoefficientBassRaw1PolynomialInputCap.laurent P β p q w
      (mapParameter (precompNode
        (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p)) y) at h
  rw [h]
  exact input_place_laurent P β p q w _

/-- The actual second plus cell agrees in the full fixed polynomial triple sheet. -/
theorem plus_second_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q
        (1, upper (lower t))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurent R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurent R) p q w (1, lower t)) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_second]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_first, input_precomp_laurent]
  have h := CoefficientBassRaw1PolynomialPostcomp.plus_laurent P p q w
    (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurent R) p q)
      (NativeSquareFiveSimplex.parameter t))
  rw [plus_lower_iso] at h
  exact h.trans (congrArg _ (second_family P (underToLaurent R) p q w t))

/-- The actual second minus cell retains its inverse chart and independent square clock. -/
theorem minus_second_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q
        (1, upper (lower t))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurentInvert R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurentInvert R) p q w
        (1, lower t)) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_second]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_first, input_precomp_laurent]
  have h := CoefficientBassRaw1PolynomialPostcomp.minus_laurent P p q w
    (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P
      (underToLaurentInvert R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P
        (underToLaurentInvert R) p q)
      (NativeSquareFiveSimplex.parameter t))
  rw [minus_lower_iso] at h
  exact h.trans (congrArg _ (second_family P (underToLaurentInvert R) p q w t))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputSecondCell
