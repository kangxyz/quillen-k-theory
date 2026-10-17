/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositePathCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleLowerFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1ChartCompositionEndpoints

/-! The actual first chart cell of the final postcomposition and input-cap seam. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputFirstCell
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialTripleAnchor BassH0Merge BassH1Join
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- Every original first composite node is retained under actual postcomposition. -/
def postcompFirstNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (postcompLowerIso P β p q w)
    (postcompNode (normalizedMap (laurentArrow P w))
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β p q i))

/-- The terminal input column retains both actual placement reference transports. -/
def inputFirstNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β p q w)
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm
      (CoefficientBassRaw1ChartCompositionProduct.columnNodes P β p q w 2 i))

private theorem pair_first_two :
    CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β p q 2 =
    CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
      (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
        (CoefficientBassLaurentCompositionCarrier.nodes P p q 2)) := by
  exact (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes P β p q 2).symm.trans
    (CoefficientBassRaw1PolynomialLowerAttachment.sheet_target_nodes P β p q 2)

private theorem common_node : postcompFirstNodes P β p q w 2 = inputFirstNodes P β p q w 2 := by
  rw [postcompFirstNodes, pair_first_two]
  exact (CoefficientBassRaw1PolynomialTripleLowerFaces.postcomp_node_row P β p q w 2).trans
    (CoefficientBassRaw1PolynomialTripleLowerFaces.input_node_row P β p q w 2).symm

/-- The complete first chart rows match before any native evaluation. -/
theorem first_nodes (i : Fin 5) :
    postcompFirstNodes P β p q w i = inputFirstNodes P β p q w i := by
  apply post_families_match
    (polynomialReference P p q w ≫ normalizedMap (chart P β d))
    (normalizedMap (laurentArrow P q) ≫ normalizedMap (laurentArrow P w))
    (CoefficientBassRaw1ChartCompositionProduct.chartReference P β p)
    (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β p)
    (ρ := postcompLowerIso P β p q w ≪≫
      isoWhiskerRight
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β p q ≪≫
          CoefficientMovingSquareRows.firstAnchor
            (coefficientMap P ((polynomialUnderFunctor R).map p))
            (coefficientMap P ((polynomialUnderFunctor R).map q))
            (coefficientMap P ((laurentUnderFunctor R).map p))
            (coefficientMap P ((laurentUnderFunctor R).map q))
            (coefficientMap P (β.app a)) (coefficientMap P (β.app b))
            (coefficientMap P (β.app c))
            (coefficientMap_naturality P β p).symm
            (coefficientMap_naturality P β q).symm)
        (normalizedMap (laurentArrow P w)).functor)
    («σ» := inputLowerIso P β p q w ≪≫
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm ≪≫
      isoWhiskerLeft (CoefficientBassRaw1ChartCompositionProduct.chartReference P β p).functor
        (CoefficientBassLaurentCompositionCarrier.nodes P q w 2).2)
    ?_ ?_ 2 (common_node P β p q w) i
  · intro j
    simp only [postcompFirstNodes,
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes,
      CommonReferenceProduct.reanchor, postcompNode, postReferenceNode,
      isoWhiskerRight_trans, Iso.trans_assoc]
    rfl
  · intro j
    simp only [inputFirstNodes, CoefficientBassRaw1ChartCompositionProduct.columnNodes,
      CommonReferenceProduct.reanchor, CommonReferenceProduct.node,
      composition_pair_iso_other, postReferenceNode, Iso.refl_trans, Iso.trans_assoc]
    rfl

/-- The entire terminal input column keeps the original chart-square clock. -/
theorem first_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P β p q w))
      (mapParameter (postcompNode (normalizedMap (laurentArrow P w)))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q)
          (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β p q)
          (NativeSquareFiveSimplex.parameter t))) =
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β p q w))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β p q w).symm)
        (CoefficientBassRaw1ChartCompositionProduct.family P β p q w (1, t))) := by
  rw [CoefficientBassRaw1ChartCompositionProduct.family_one, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N ↦ parameter
    (polynomialReference P p q w ≫ normalizedMap (chart P β d)) N
    (NativeSquareFiveSimplex.parameter t)) (funext (first_nodes P β p q w))

/-- The lower half of the actual final plus seam agrees in the full polynomial triple sheet. -/
theorem plus_first_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (1, lower t)) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurent R) p q w
      (CoefficientBassRaw1PolynomialInputCap.first P (underToLaurent R) p q w (1, t)) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_first]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.first, ContinuousMap.comp_apply]
  rw [input_place_laurent]
  have h := CoefficientBassRaw1PolynomialPostcomp.plus_laurent P p q w
    (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurent R) p q)
      (NativeSquareFiveSimplex.parameter t))
  rw [plus_lower_iso] at h
  exact h.trans (congrArg _ (first_family P (underToLaurent R) p q w t))

/-- The lower half of the actual final minus seam keeps the inverse chart and the same clock. -/
theorem minus_first_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q
        (1, lower t)) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurentInvert R) p q w
      (CoefficientBassRaw1PolynomialInputCap.first P (underToLaurentInvert R) p q w (1, t)) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_first]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.first, ContinuousMap.comp_apply]
  rw [input_place_laurent]
  have h := CoefficientBassRaw1PolynomialPostcomp.minus_laurent P p q w
    (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P
      (underToLaurentInvert R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P
        (underToLaurentInvert R) p q)
      (NativeSquareFiveSimplex.parameter t))
  rw [minus_lower_iso] at h
  exact h.trans (congrArg _ (first_family P (underToLaurentInvert R) p q w t))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputFirstCell
