/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0C0SeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1WholeOldSeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFaceLoopFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedRoutes

/-! The actual right carrier route, retaining the original outer half and quarter cuts. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveActualRightRoute
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0Conjugation
open CoefficientBassPositiveJ0C0SeedAlignment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The two carrier tips remain separate. -/
abbrev minusTip := CutOpenCarrier.tipMinus (polyRef P d) (chart P d) (laurentRef P d)
  (ordinary P d) (shifted P d)
/-- The plus tip is not identified with the minus tip. -/
abbrev plusTip := CutOpenCarrier.tipPlus (polyRef P d) (chart P d) (laurentRef P d)
  (ordinary P d) (shifted P d)

/-- The prescribed initial carrier path is the complete C0 target seed. -/
def start : C(I, Carrier P d) :=
  ⟨fun s ↦ toJ0 P d (CoefficientBassPositiveC0CarrierSeed.face P
    (firstArrow d) (secondArrow d) (1, s)), by fun_prop⟩
/-- The final carrier path retains the entire C1 endpoint word. -/
def finish : C(I, Carrier P d) :=
  ⟨fun s ↦ CoefficientBassPositiveC1SeedFace.face P
    (firstArrow d) (secondArrow d) (1, s), by fun_prop⟩

/-- The single reversed C0 segment meets the complete new seed. -/
def c0 : (start P d).Homotopy (targetWord P d).toContinuousMap where
  toFun z := toJ0 P d (CoefficientBassPositiveC0CarrierSeed.reversedFace P
    (firstArrow d) (secondArrow d) z)
  continuous_toFun := by fun_prop
  map_zero_left s := congrArg (toJ0 P d)
    (CoefficientBassPositiveC0CarrierSeed.reversedFace_source P
      (firstArrow d) (secondArrow d) s)
  map_one_left s := CoefficientBassPositiveJ0C0SeedSeam.reversedFace_exit P d s

/-- The C1 entrance equals the entire old seed, before evaluation. -/
def c1 : (sourceWord P d).toContinuousMap.Homotopy (finish P d) where
  toFun z := CoefficientBassPositiveC1SeedFace.face P (firstArrow d) (secondArrow d) z
  continuous_toFun := by fun_prop
  map_zero_left s := CoefficientBassPositiveC1WholeOldSeedSeam.face_zero P d s
  map_one_left _ := rfl

/-- Original route time: C0 on the first half, J0 on the next quarter, C1 on the last quarter. -/
def routeHomotopy : (start P d).Homotopy (finish P d) :=
  (c0 P d).trans ((reverseComparison P d).toHomotopy.trans (c1 P d))
/-- Route and seed coordinates are independent. -/
def route : C(I × I, Carrier P d) := (routeHomotopy P d).toContinuousMap

theorem route_start (s : I) : route P d (0, s) = start P d s :=
  (routeHomotopy P d).apply_zero s

theorem route_finish (s : I) : route P d (1, s) = finish P d s :=
  (routeHomotopy P d).apply_one s

theorem c0_bottom (r : I) : c0 P d (r, 0) = minusTip P d := by
  change toJ0 P d (CoefficientBassPositiveC0CarrierSeed.face P
    (firstArrow d) (secondArrow d) (unitInterval.symm r, 0)) = _
  rw [CoefficientBassPositiveC0CarrierSeed.face_bottom]
  rfl

theorem c0_top (r : I) : c0 P d (r, 1) = plusTip P d := by
  change toJ0 P d (CoefficientBassPositiveC0CarrierSeed.face P
    (firstArrow d) (secondArrow d) (unitInterval.symm r, 1)) = _
  rw [CoefficientBassPositiveC0CarrierSeed.face_top]
  rfl

theorem route_bottom (r : I) : route P d (r, 0) = minusTip P d := by
  change ((c0 P d).trans ((reverseComparison P d).toHomotopy.trans (c1 P d))) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_bottom P d _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact (reverseComparison P d).source _
    · exact CoefficientBassPositiveC1SeedFace.face_bottom P (firstArrow d) (secondArrow d) _

theorem route_top (r : I) : route P d (r, 1) = plusTip P d := by
  change ((c0 P d).trans ((reverseComparison P d).toHomotopy.trans (c1 P d))) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_top P d _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact (reverseComparison P d).target _
    · exact CoefficientBassPositiveC1SeedFace.face_top P (firstArrow d) (secondArrow d) _

/-- Exact supported-right recovery, with arbitrary degree and independent route/seed/input times. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (route P d (r, s)) x =
      Path.toContinuousMap ((CoefficientBassPositiveMixedRoutes.supportedRight P d).level n
        (r, x)) s := by
  let H0 := ((boundedFlatCoefficientLaurentPlusHomotopy P d).postcomp
    (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d))).symm
  let J := (boundedFlatCoefficientBassPositiveTransitionHomotopy P (arrow d)).symm
  let H1 := (Homotopy.precomp (boundedFlatCoefficientBassPositiveConeSeed P d)
    (CoefficientBassPositiveMixedRoutes.positiveComposition P d)).cast rfl
      (Category.assoc _ _ _).symm
  change _ = Path.toContinuousMap ((H0.trans (J.trans H1)).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (c0 P d)
    ((reverseComparison P d).toHomotopy.trans (c1 P d))
    (H0.levelHomotopy n).toHomotopy ((J.trans H1).levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    exact CoefficientBassPositiveC0CarrierSeedNative.actual_original_C0 P d n t s x
  · intro t
    refine ContinuousMap.Homotopy.Evaluation.trans_compare
      (reverseComparison P d).toHomotopy (c1 P d)
      (J.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
      (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
        (ordinary P d) (shifted P d) n y x)
      (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ t
    · intro v
      exact reverseComparison_transition P d n v s x
    · intro v
      dsimp only [H1, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp,
        CoefficientBassPositiveMixedRoutes.positiveComposition]
      dsimp only [c1]
      have h := CoefficientBassPositiveC1SeedFaceNative.face_native P
        ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) n v s x
      dsimp only [CoefficientBassPositiveC1SeedFaceNative.evaluate] at h
      dsimp only [polyRef, CoefficientBassPositiveJ0PolynomialMovement.reference,
        chart, laurentRef, ordinary, shifted, firstArrow, secondArrow]
      exact h

end Quillen.PerfectComplexes.CoefficientBassPositiveActualRightRoute
