/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompLowerNodes

/-! The prescribed lower face of both original postcomposed polynomial caps. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

private theorem maps_comp {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{u}}
    {F : V₀ ⟶ W₀} {G : V₁ ⟶ W₁} {H : V₂ ⟶ W₂}
    (g : Node G → Node H) (f : Node F → Node G) (y : |parameterSSet F|) :
    mapParameter g (mapParameter f y) = mapParameter (fun x ↦ g (f x)) y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The complete lower family is transported before the sheet inclusion. -/
theorem postcomp_lower_family (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P β p q w))
      (mapParameter (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)))
        (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 0))) =
    mapParameter (fun N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q) ↦
      CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
        (precompNode (BassMWholeNerve.coefficientModel P (β.app a))
          (CommonReferenceProduct.reanchor (NormalizedTripleSimplex.leftFirst
            (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
            (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)) N))))
      (CoefficientBassLaurentCompositionCarrier.family P p q r) := by
  rw [CoefficientBassRaw1PolynomialLowerAttachment.sheetFamily_lower,
    maps_comp, maps_comp]
  exact postcomp_lower_parameter P β p q w
    (CoefficientBassLaurentCompositionCarrier.family P p q r)

/-- The actual plus placement has the exact fixed lower reference before evaluation. -/
theorem plus_lower_iso :
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.M P w)
      (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
        CoefficientBassSeedTargetChartAttachment.L P w)
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c))
        (Iso.refl _))
      (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) =
    postcompLowerIso P (underToLaurent R) p q w := by
  dsimp only [CoefficientBassPolynomialSheetNormalization.laurentIso]
  rw [plus_targetAnchor]
  rfl

/-- The entire plus cap lower face is the fixed Laurent triple left route. -/
theorem plus_postcomp_lower_family (r : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (r, 0)) =
    SSet.toTop.map (left₀ (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      (CoefficientBassRaw1PolynomialPostcomp.reference P p q w ≫
        CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (Iso.refl _))
      (mapParameter (fun N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q) ↦
        CommonReferenceProduct.reanchor (referenceIso P (underToLaurent R) p q w).symm
          (precompNode (BassMWholeNerve.coefficientModel P ((underToLaurent R).app a))
            (CommonReferenceProduct.reanchor
              (NormalizedTripleSimplex.leftFirst
                (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
              (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)) N))))
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  have h := CoefficientBassRaw1PolynomialPostcomp.plus_laurent P p q w
    (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P (underToLaurent R) p q (r, 0))
  rw [plus_lower_iso] at h
  have hc := congrArg (CoefficientBassRaw1PolynomialPostcomp.plus P p q w)
    (CoefficientBassRaw1PolynomialPairCone.corrected_left P (underToLaurent R) p q r)
  have hn := postcomp_lower_family P p q w (underToLaurent R) r
  exact hc.trans (h.trans (congrArg _ hn))

/-- The actual minus placement has the exact fixed lower reference before evaluation. -/
theorem minus_lower_iso :
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.M P w)
      (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
        CoefficientBassNegativeTargetChartAttachment.L P w)
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c))
        (Iso.refl _))
      (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) =
    postcompLowerIso P (underToLaurentInvert R) p q w := by
  dsimp only [CoefficientBassPolynomialSheetNormalization.laurentIso]
  rw [minus_targetAnchor]
  rfl

/-- The entire minus cap lower face is the fixed Laurent triple left route. -/
theorem minus_postcomp_lower_family (r : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (r, 0)) =
    SSet.toTop.map (left₀ (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      (CoefficientBassRaw1PolynomialPostcomp.reference P p q w ≫
        CoefficientBassNegativeTargetChartAttachment.Jb P (b := d)) (Iso.refl _))
      (mapParameter (fun N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q) ↦
        CommonReferenceProduct.reanchor (referenceIso P (underToLaurentInvert R) p q w).symm
          (precompNode (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app a))
            (CommonReferenceProduct.reanchor
              (NormalizedTripleSimplex.leftFirst
                (laurentArrow P w) (laurentArrow P q) (laurentArrow P p))
              (postcompNode (BassH0Merge.normalizedMap (laurentArrow P w)) N))))
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  have h := CoefficientBassRaw1PolynomialPostcomp.minus_laurent P p q w
    (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P (underToLaurentInvert R) p q (r, 0))
  rw [minus_lower_iso] at h
  have hc := congrArg (CoefficientBassRaw1PolynomialPostcomp.minus P p q w)
    (CoefficientBassRaw1PolynomialPairCone.corrected_left P (underToLaurentInvert R) p q r)
  have hn := postcomp_lower_family P p q w (underToLaurentInvert R) r
  exact hc.trans (h.trans (congrArg _ hn))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
