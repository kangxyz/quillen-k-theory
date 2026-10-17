/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualLeftRouteNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMixedRoutes

/-! The inverse outer chart uses the same full-reference left constructions at its actual q. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeActualLeftRoute
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveLeftComparisons CoefficientBassPositiveActualLeftRoute
open CoefficientBassPositiveLeftComparisonNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The coefficient inclusion from `d` into its polynomial extension. -/
abbrev pArrow := (polynomialUnderCoefficient R).app d
/-- The inverse-coordinate map from the polynomial extension of `d` to its Laurent extension. -/
abbrev qArrow := (underToLaurentInvert R).app d
/-- The polynomial reference for the inverse-coordinate coefficient factorization. -/
abbrev polyRef := polynomialReference P (pArrow d) (qArrow d)
/-- The Laurent reference for the inverse-coordinate coefficient factorization. -/
abbrev laurentRef := laurentReference P (pArrow d) (qArrow d)
/-- The chart map at the terminal Laurent coefficient object. -/
abbrev chart := chartMap P (c := (laurentUnderFunctor R).obj d)
/-- The reference isomorphism from the Laurent reference to the polynomial reference followed by
the chart. -/
abbrev ordinary := ordinaryAnchor P (pArrow d) (qArrow d)
/-- The ordinary anchor preceded by the forward Laurent-unit automorphism. -/
abbrev shifted := LaurentUnitReferenceSpecialization.shiftedAnchor P (pArrow d) (qArrow d)
/-- The two-tip carrier for the inverse-coordinate coefficient factorization. -/
abbrev Carrier := CoefficientBassPositiveC0CarrierSeed.Carrier P (pArrow d) (qArrow d)
/-- The tip of the ordinary polynomial attachment. -/
abbrev minusTip := CutOpenCarrier.tipMinus (polyRef P d) (chart P d) (laurentRef P d)
  (ordinary P d) (shifted P d)
/-- The tip of the Laurent-unit shifted polynomial attachment. -/
abbrev plusTip := CutOpenCarrier.tipPlus (polyRef P d) (chart P d) (laurentRef P d)
  (ordinary P d) (shifted P d)

/-- The complete target C0 seed at its original time. -/
def start : C(unitInterval, Carrier P d) :=
  ⟨fun s ↦ CoefficientBassPositiveC0CarrierSeed.face P (pArrow d) (qArrow d) (1, s),
    by fun_prop⟩
/-- The complete target C1 seed, with its forward inner unit. -/
def finish : C(unitInterval, Carrier P d) :=
  ⟨fun s ↦ CoefficientBassPositiveC1SeedFace.face P (pArrow d) (qArrow d) (1, s),
    by fun_prop⟩

/-- The common midpoint is the whole first-target seed. -/
def middlePath : C(I, Carrier P d) :=
  (firstTargetWord P (pArrow d) (qArrow d)).toContinuousMap

/-- Reverse the middle comparison exactly once, retaining its own full seed coordinate. -/
def middle : (start P d).Homotopy (middlePath P d) where
  toFun z := middleComparison P (pArrow d) (qArrow d) (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact ((middleComparison P (pArrow d) (qArrow d)).apply_one s).trans
      ((middle_target_seed P (pArrow d) (qArrow d) s).trans
        (CoefficientBassPositiveLeftStartingSeed.starting_seed_target P
          (pArrow d) (qArrow d) s))
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((middleComparison P (pArrow d) (qArrow d)).apply_zero s).trans
      (midpoint P (pArrow d) (qArrow d) s)

/-- Reverse the first comparison exactly once and use its proved entire terminal seed. -/
def first : (middlePath P d).Homotopy (finish P d) where
  toFun z := firstComparison P (pArrow d) (qArrow d) (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact (firstComparison P (pArrow d) (qArrow d)).apply_one s
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((firstComparison P (pArrow d) (qArrow d)).apply_zero s).trans
      ((first_source_seed P (pArrow d) (qArrow d) s).trans
        (CoefficientBassPositiveLeftTerminalSeed.terminal_parameter P
          (pArrow d) (qArrow d) s))

/-- The original outer order: reversed middle on the first half, reversed first on the second. -/
def routeHomotopy : (start P d).Homotopy
    (finish P d) := (middle P d).trans (first P d)

/-- The actual left route is jointly continuous in original route and seed time. -/
def route : C(I × I, Carrier P d) :=
  (routeHomotopy P d).toContinuousMap

theorem route_start (s : I) : route P d (0, s) =
    start P d s := (routeHomotopy P d).apply_zero s

theorem route_finish (s : I) : route P d (1, s) =
    finish P d s := (routeHomotopy P d).apply_one s

theorem route_bottom (r : I) : route P d (r, 0) =
    minusTip P d := by
  change ((middle P d).trans (first P d)) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P (pArrow d) (qArrow d)).source _
  · exact (firstComparison P (pArrow d) (qArrow d)).source _

theorem route_top (r : I) : route P d (r, 1) =
    plusTip P d := by
  change ((middle P d).trans (first P d)) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P (pArrow d) (qArrow d)).target _
  · exact (firstComparison P (pArrow d) (qArrow d)).target _


/-- All native degrees, the entire input, and the two original outer reverse clocks are retained. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (route P d (r, s)) x =
      Path.toContinuousMap ((CoefficientBassNegativeMixedRoutes.supportedLeft P d).level n
        (r, x)) s := by
  let H0 := (Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app d)))
    (boundedFlatCoefficientBassPositiveTransitionHomotopy P
      ((underToLaurentInvert R).app d)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  let H1 := (boundedFlatCoefficientBassPositiveTransitionHomotopy P
    ((polynomialUnderCoefficient R).app d)).symm.postcomp
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P
        ((underToLaurentInvert R).app d)))
  change _ = Path.toContinuousMap ((H0.trans H1).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (middle P d) (first P d)
    (H0.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    have h := middle_comparison_transition P ((polynomialUnderCoefficient R).app d)
      ((underToLaurentInvert R).app d) n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H0, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp,
      Homotopy.symm, middle, polyRef,
      chart, laurentRef, ordinary, shifted, pArrow, qArrow]
    exact h
  · intro t
    have h := first_comparison_transition P ((polynomialUnderCoefficient R).app d)
      ((underToLaurentInvert R).app d) n (unitInterval.symm t) s x
    dsimp only [CoefficientBassPositiveLeftNativeFamilies.nativeValue] at h
    dsimp only [H1, Homotopy.levelHomotopy, Homotopy.postcomp, Homotopy.symm,
      first, polyRef,
      chart, laurentRef, ordinary, shifted, pArrow, qArrow]
    exact h

end Quillen.PerfectComplexes.CoefficientBassNegativeActualLeftRoute
