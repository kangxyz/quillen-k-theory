/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMovingSquarePause
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCommonChartSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered

/-! The original paused polynomial chart square as a full reference-nerve surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPausedChart
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete original chart reference has genuine polynomial input. -/
abbrev reference := NormalizedTripleSimplex.sourceMap (coefficientMap P (β.app c))
  (coefficientMap P ((polynomialUnderFunctor R).map q))
  (coefficientMap P ((polynomialUnderFunctor R).map p))

/-- All eighteen original chart nodes, including their normalization anchors. -/
abbrev nodes := BassOverlap.chartNodes P p q β

/-- The original terminal pause is retained in the scalar surface itself. -/
def family : C(I × I, |nerve (Codiscrete (Node (reference P β p q)))|) :=
  (parameter (reference P β p q) (nodes P β p q)).comp
    DoubleSquareScalarPaths.coefficientPausedSquareParameter

/-- Every degree and arbitrary polynomial input recovers the prescribed paused square. -/
theorem family_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily (reference P β p q) n (family P β p q (r, s)) x =
      ((CoefficientTransformationComposition.movingSquare P β p q).pauseRight).level n
        (r, (s, x)) := by
  dsimp only [family, ContinuousMap.comp_apply]
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  exact CoefficientTransformationComposition.Scalar.pausedSquare_native P β p q n r s x

/-- The actual normalized polynomial pair reference, before the target chart. -/
abbrev polynomialReference := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P ((polynomialUnderFunctor R).map q))
  (coefficientMap P ((polynomialUnderFunctor R).map p))

/-- The full target reference of the pair's literal single polynomial sheet. -/
abbrev sheetReference := polynomialReference P p q ≫
  BassMWholeNerve.coefficientModel P (β.app c)

/-- The original binary normalization places the entire paused square in that sheet. -/
def sheetAnchor : (sheetReference P β p q).functor ≅ (reference P β p q).functor :=
  (BinaryNormalizationSimplex.total (coefficientMap P (β.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
      coefficientMap P ((polynomialUnderFunctor R).map p))).symm

/-- The reanchored surface retains the original eighteen nodes and paused clock. -/
def sheetFamily : C(I × I, |nerve (Codiscrete (Node (sheetReference P β p q)))|) :=
  (mapParameter (CommonReferenceProduct.reanchor (sheetAnchor P β p q))).comp
    (family P β p q)

/-- Full reanchoring preserves the prescribed original square on arbitrary polynomial input. -/
theorem sheetFamily_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily (sheetReference P β p q) n (sheetFamily P β p q (r, s)) x =
      ((CoefficientTransformationComposition.movingSquare P β p q).pauseRight).level n
        (r, (s, x)) := by
  dsimp only [sheetFamily, ContinuousMap.comp_apply]
  rw [pointwise_reanchor, family_native]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPausedChart
