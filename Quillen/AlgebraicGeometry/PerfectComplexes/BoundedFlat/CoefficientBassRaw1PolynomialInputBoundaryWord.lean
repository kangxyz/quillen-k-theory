/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPlacement

/-! The exact endpoint word of the original chart-square half of a polynomial cap. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The two full original chart endpoints retain the inverse naturality transport. -/
theorem input_chart_boundary_word :
    (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 4).2.symm ≪≫
      (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2).2 =
        (binaryChartIso P β f).symm := by
  change (NativeSquareFiveSimplex.sourceIso
    (laurentArrow P f) (chart P β a) (chart P β b) (polynomialArrow P f)
    (coefficientMap_naturality P β f) ≪≫
      BinaryNormalizationSimplex.total (chart P β b) (polynomialArrow P f)).symm ≪≫
    BinaryNormalizationSimplex.total (laurentArrow P f) (chart P β a) = _
  simp only [binaryChartIso, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]

/-- The midpoint transport keeps exactly the original inverse chart-square word. -/
theorem input_midpoint_word {c d : Under R} (p : b ⟶ c) (q : c ⟶ d) :
    isoWhiskerRight (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q)
        (BassMWholeNerve.coefficientModel P (β.app d)).functor ≪≫
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm ≪≫
        isoWhiskerRight
          (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2).2
          (CoefficientBassLaurentCompositionCarrier.reference P p q).functor =
    isoWhiskerRight (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q)
        (BassMWholeNerve.coefficientModel P (β.app d)).functor ≪≫
      isoWhiskerLeft
        (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f).functor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q) ≪≫
      isoWhiskerRight (binaryChartIso P β f).symm
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor := by
  simp only [CoefficientBassRaw1ChartCompositionProduct.midpointIso,
    Iso.trans_symm, ← isoWhiskerLeft_symm, Iso.symm_symm_eq, Iso.trans_assoc,
    isoWhiskerRight_symm, ← isoWhiskerRight_trans, input_chart_boundary_word]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
