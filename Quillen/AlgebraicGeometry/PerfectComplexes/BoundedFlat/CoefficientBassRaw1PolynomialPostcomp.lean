/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTargetSingleFactor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetSingleFactor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCone

/-! The actual postcomposed polynomial cap in its fixed triple reference sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original paused-chart polynomial reference for the pair `p`, `q`. -/
abbrev pair := CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
/-- The original coefficient map after polynomial extension of `p`. -/
abbrev firstArrow := coefficientMap P ((polynomialUnderFunctor R).map p)
/-- The original coefficient map after polynomial extension of `q`. -/
abbrev secondArrow := coefficientMap P ((polynomialUnderFunctor R).map q)
/-- The original coefficient map after polynomial extension of the last arrow `w`. -/
abbrev lastArrow := coefficientMap P ((polynomialUnderFunctor R).map w)

/-- The target reference is the literal original polynomial-indexed normalized triple. -/
abbrev reference := NormalizedTripleSimplex.sourceMap
  (lastArrow P w) (secondArrow P q) (firstArrow P p)

/-- The old pair followed by the polynomial action is normalized by the original left route. -/
def polynomialIso : (reference P p q w).functor ≅
    (pair P p q ≫ BassH0Merge.normalizedMap (lastArrow P w)).functor :=
  NormalizedTripleSimplex.leftFirst (lastArrow P w) (secondArrow P q) (firstArrow P p)

/-- The actual chart's single sheet retains the full polynomial triple and its own tip. -/
abbrev carrier (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) :=
  |firstSimplicial (reference P p q w) (BassMWholeNerve.coefficientModel P (β.app d))
    (reference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d)) (Iso.refl _)|

/-- The positive original target action is factored through its first sheet before reanchoring. -/
def plus : C(CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q,
    carrier P p q w (underToLaurent R)) :=
  (CoefficientBassPolynomialSheetNormalization.map
    (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M P w)
    (reference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w (pair P p q)
      (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (polynomialIso P p q w)).comp
      (CoefficientBassPositiveTargetSingleSheet.firstMap P w (pair P p q)
        (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))

/-- The negative target action retains its actual minus square and outer clocks. -/
def minus : C(CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q,
    carrier P p q w (underToLaurentInvert R)) :=
  (CoefficientBassPolynomialSheetNormalization.map
    (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.M P w)
    (reference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w (pair P p q)
      (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (polynomialIso P p q w)).comp
      (CoefficientBassNegativeTargetSingleSheet.firstMap P w (pair P p q)
        (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
