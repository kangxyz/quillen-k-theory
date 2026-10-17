/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceCylinder
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialCaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompCells

/-! Direct original coefficient actions on the genuine identity-source polynomial cylinder. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairDirectAction
open CommonReferenceNerve CoefficientBassRaw1PolynomialSourceCylinder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The pair reference changes only by the original polynomial composite equality. -/
def polynomialIso :
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor ≅
      ((𝟙 (model P a)) ≫ BassMWholeNerve.coefficientModel P
        ((polynomialUnderFunctor R).map (p ≫ q))).functor :=
  CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso P p q ≪≫
    (Functor.leftUnitor (BassMWholeNerve.coefficientModel P
      ((polynomialUnderFunctor R).map (p ≫ q))).functor).symm

/-- The actual plus direct action keeps its prescribed chart-then-cylinder path. -/
def plus : C(carrier P (underToLaurent R) a,
    CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q) :=
  (CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) (polynomialIso P p q)).comp
    (CoefficientBassPositiveTargetSingleSheet.firstMap P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _))

/-- The whole direct plus endpoint path uses every original source cylinder height. -/
def plusPath : C(I, CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q) :=
  (plus P p q).comp (cylinder P (underToLaurent R) a)

/-- The actual minus direct action keeps its prescribed chart-then-cylinder path. -/
def minus : C(carrier P (underToLaurentInvert R) a,
    CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q) :=
  (CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
    P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) (polynomialIso P p q)).comp
    (CoefficientBassNegativeTargetSingleSheet.firstMap P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _))

/-- The whole direct minus endpoint path uses every original source cylinder height. -/
def minusPath : C(I, CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R)
    p q) :=
  (minus P p q).comp (cylinder P (underToLaurentInvert R) a)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairDirectAction
