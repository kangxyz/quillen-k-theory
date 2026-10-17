/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeActualLeftRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftComparisonNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeMixedRoutes

/-! Native recovery of the original left route for arbitrary composable coefficient arrows. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeActualLeftNative
open CommonReferenceNerve CoefficientBassCompositeActualLeftRoute
open CoefficientBassPositiveLeftComparisonNative
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- All native degrees, the entire input, and the two original outer reverse clocks are retained. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (route P p q (r, s)) x =
      Path.toContinuousMap ((CoefficientBassCompositeMixedRoutes.supportedLeft P p q).level n
        (r, x)) s := by
  let H0 := (Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      q).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  let H1 := (boundedFlatCoefficientBassPositiveTransitionHomotopy P
    p).symm.postcomp
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
        q))
  change _ = Path.toContinuousMap ((H0.trans H1).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (middle P p q) (first P p q)
    (H0.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P p q) (chart P p q) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    have h := middle_comparison_transition P p
      q n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H0, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp,
      Homotopy.symm, middle, polyRef,
      chart, laurentRef, ordinary, shifted]
    exact h
  · intro t
    have h := first_comparison_transition P p
      q n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H1, Homotopy.levelHomotopy, Homotopy.postcomp, Homotopy.symm,
      first, polyRef,
      chart, laurentRef, ordinary, shifted]
    exact h


end Quillen.PerfectComplexes.CoefficientBassCompositeActualLeftNative
