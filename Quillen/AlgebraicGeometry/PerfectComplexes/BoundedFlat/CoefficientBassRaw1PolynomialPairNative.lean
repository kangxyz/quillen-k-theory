/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeConeSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers

/-! Both original polynomial chart summands retain their prescribed paused Q caps. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The plus first-sheet value in the actual Bass target cone. -/
def plusValue (n : ℕ) (z : carrier P (underToLaurent R) p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
    (evaluate P (underToLaurent R) p q n z x)

/-- The entire existing Q cap on the genuine plus polynomial summand is retained. -/
theorem plusValue_chartSquare (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P p q n (chartSquare P (underToLaurent R) p q (r, s)) x =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P c)).map n
        ((BassMWhole.comparisonSquare P p q).level n
          (r, (s, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))) := by
  rw [BassMWhole.comparison_inl]
  have h := chartSquare_native P (underToLaurent R) p q n r s x
  have hi := congrArg (fun f ↦ f.map n
    (((CoefficientTransformationComposition.movingSquare
      P (underToLaurent R) p q).pauseRight).level n
      (r, (s, x)))) (boundedFlatCoefficientBassPositiveConeInclusion_inclusion P c)
  exact (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P c).map n) h).trans hi

/-- The minus first-sheet value in the actual Bass target cone. -/
def minusValue (n : ℕ) (z : carrier P (underToLaurentInvert R) p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassNegativeConeInclusion P c).map n
    (evaluate P (underToLaurentInvert R) p q n z x)

/-- The entire existing Q cap on the genuine minus polynomial summand is retained. -/
theorem minusValue_chartSquare (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P p q n (chartSquare P (underToLaurentInvert R) p q (r, s)) x =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P c)).map n
        ((BassMWhole.comparisonSquare P p q).level n
          (r, (s, (HomotopyPushout.inr
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))) := by
  rw [BassMWhole.comparison_inr]
  have h := chartSquare_native P (underToLaurentInvert R) p q n r s x
  have hi := congrArg (fun f ↦ f.map n
    (((CoefficientTransformationComposition.movingSquare
      P (underToLaurentInvert R) p q).pauseRight).level n
      (r, (s, x)))) (boundedFlatCoefficientBassNegativeConeInclusion_inclusion P c)
  exact (congrArg ((boundedFlatCoefficientBassNegativeConeInclusion P c).map n) h).trans hi

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
