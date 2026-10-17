/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualLeftRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftComparisonNative

/-! Recover the exact original supported left route from its actual continuous carrier surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveActualLeftRoute
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveLeftComparisonNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- All native degrees, the entire input, and the two original outer reverse clocks are retained. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (route P d (r, s)) x =
      Path.toContinuousMap ((CoefficientBassPositiveMixedRoutes.supportedLeft P d).level n
        (r, x)) s := by
  let H0 := (Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app d)))
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      ((underToLaurent R).app d)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  let H1 := (boundedFlatCoefficientBassPositiveTransitionHomotopy P
    ((polynomialUnderCoefficient R).app d)).symm.postcomp
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
        ((underToLaurent R).app d)))
  change _ = Path.toContinuousMap ((H0.trans H1).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (middle P d) (first P d)
    (H0.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    have h := middle_comparison_transition P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H0, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp,
      Homotopy.symm, middle, polyRef, CoefficientBassPositiveJ0PolynomialMovement.reference,
      chart, laurentRef, ordinary, shifted, firstArrow, secondArrow]
    exact h
  · intro t
    have h := first_comparison_transition P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H1, Homotopy.levelHomotopy, Homotopy.postcomp, Homotopy.symm,
      first, polyRef, CoefficientBassPositiveJ0PolynomialMovement.reference,
      chart, laurentRef, ordinary, shifted, firstArrow, secondArrow]
    exact h

end Quillen.PerfectComplexes.CoefficientBassPositiveActualLeftRoute
