/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualLeftRoute

/-! The original full-reference left surface for arbitrary composable coefficient arrows. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeActualLeftRoute
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveLeftComparisons CoefficientBassPositiveActualLeftRoute
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The full polynomial reference for the original composable coefficient arrows `p` and `q`. -/
abbrev polyRef := polynomialReference P p q
/-- The full Laurent reference for the same original coefficient arrows `p` and `q`. -/
abbrev laurentRef := laurentReference P p q
/-- The original chart map at the target coefficient object `c`. -/
abbrev chart (_p : a ⟶ b) (_q : b ⟶ c) := chartMap P (c := c)
/-- The ordinary polynomial-to-Laurent anchor for the original pair `p`, `q`. -/
abbrev ordinary := ordinaryAnchor P p q
/-- The shifted Laurent-unit anchor for the original pair `p`, `q`. -/
abbrev shifted := LaurentUnitReferenceSpecialization.shiftedAnchor P p q
/-- The original positive C0 seed carrier for the composable arrows `p` and `q`. -/
abbrev Carrier := CoefficientBassPositiveC0CarrierSeed.Carrier P p q
/-- The minus tip of the original cut-open carrier with its ordinary and shifted anchors. -/
abbrev minusTip := CutOpenCarrier.tipMinus (polyRef P p q) (chart P p q) (laurentRef P p q)
  (ordinary P p q) (shifted P p q)
/-- The separate plus tip of the same original cut-open carrier. -/
abbrev plusTip := CutOpenCarrier.tipPlus (polyRef P p q) (chart P p q) (laurentRef P p q)
  (ordinary P p q) (shifted P p q)

/-- The complete target C0 seed at its original time. -/
def start : C(unitInterval, Carrier P p q) :=
  ⟨fun s ↦ CoefficientBassPositiveC0CarrierSeed.face P p q (1, s),
    by fun_prop⟩
/-- The complete target C1 seed, with its forward inner unit. -/
def finish : C(unitInterval, Carrier P p q) :=
  ⟨fun s ↦ CoefficientBassPositiveC1SeedFace.face P p q (1, s),
    by fun_prop⟩

/-- The common midpoint is the whole first-target seed. -/
def middlePath : C(I, Carrier P p q) :=
  (firstTargetWord P p q).toContinuousMap

/-- Reverse the middle comparison exactly once, retaining its own full seed coordinate. -/
def middle : (start P p q).Homotopy (middlePath P p q) where
  toFun z := middleComparison P p q (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact ((middleComparison P p q).apply_one s).trans
      ((middle_target_seed P p q s).trans
        (CoefficientBassPositiveLeftStartingSeed.starting_seed_target P
          p q s))
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((middleComparison P p q).apply_zero s).trans
      (midpoint P p q s)

/-- Reverse the first comparison exactly once and use its proved entire terminal seed. -/
def first : (middlePath P p q).Homotopy (finish P p q) where
  toFun z := firstComparison P p q (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact (firstComparison P p q).apply_one s
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((firstComparison P p q).apply_zero s).trans
      ((first_source_seed P p q s).trans
        (CoefficientBassPositiveLeftTerminalSeed.terminal_parameter P
          p q s))

/-- The original outer order: reversed middle on the first half, reversed first on the second. -/
def routeHomotopy : (start P p q).Homotopy
    (finish P p q) := (middle P p q).trans (first P p q)

/-- The actual left route is jointly continuous in original route and seed time. -/
def route : C(I × I, Carrier P p q) :=
  (routeHomotopy P p q).toContinuousMap

theorem route_start (s : I) : route P p q (0, s) =
    start P p q s := (routeHomotopy P p q).apply_zero s

theorem route_finish (s : I) : route P p q (1, s) =
    finish P p q s := (routeHomotopy P p q).apply_one s

theorem route_bottom (r : I) : route P p q (r, 0) =
    minusTip P p q := by
  change ((middle P p q).trans (first P p q)) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P p q).source _
  · exact (firstComparison P p q).source _

theorem route_top (r : I) : route P p q (r, 1) =
    plusTip P p q := by
  change ((middle P p q).trans (first P p q)) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P p q).target _
  · exact (firstComparison P p q).target _

end Quillen.PerfectComplexes.CoefficientBassCompositeActualLeftRoute
