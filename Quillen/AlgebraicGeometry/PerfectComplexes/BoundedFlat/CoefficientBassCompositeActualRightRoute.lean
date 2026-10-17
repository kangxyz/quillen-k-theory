/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0C0SeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeC1WholeOldSeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFaceLoopFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeMixedRoutes

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeActualRightRoute
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0Conjugation
open CoefficientBassCompositeJ0C0SeedAlignment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The two carrier tips remain separate. -/
abbrev minusTip := CutOpenCarrier.tipMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
  (ordinary P p q) (shifted P p q)
/-- The plus tip is not identified with the minus tip. -/
abbrev plusTip := CutOpenCarrier.tipPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
  (ordinary P p q) (shifted P p q)

/-- The prescribed initial carrier path is the complete C0 target seed. -/
def start : C(I, Carrier P p q) :=
  ⟨fun s ↦ toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.face P
    p q (1, s)), by fun_prop⟩
/-- The final carrier path retains the entire C1 endpoint word. -/
def finish : C(I, Carrier P p q) :=
  ⟨fun s ↦ CoefficientBassPositiveC1SeedFace.face P
    p q (1, s), by fun_prop⟩

/-- The single reversed C0 segment meets the complete new seed. -/
def c0 : (start P p q).Homotopy (targetWord P p q).toContinuousMap where
  toFun z := toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.reversedFace P
    p q z)
  continuous_toFun := by fun_prop
  map_zero_left s := congrArg (toJ0 P p q)
    (CoefficientBassPositiveC0CarrierSeed.reversedFace_source P
      p q s)
  map_one_left s := CoefficientBassCompositeJ0C0SeedSeam.reversedFace_exit P p q s

/-- The C1 entrance equals the entire old seed, before evaluation. -/
def c1 : (sourceWord P p q).toContinuousMap.Homotopy (finish P p q) where
  toFun z := CoefficientBassPositiveC1SeedFace.face P p q z
  continuous_toFun := by fun_prop
  map_zero_left s := CoefficientBassCompositeC1WholeOldSeedSeam.face_zero P p q s
  map_one_left _ := rfl

/-- Original route time: C0 on the first half, J0 on the next quarter, C1 on the last quarter. -/
def routeHomotopy : (start P p q).Homotopy (finish P p q) :=
  (c0 P p q).trans ((reverseComparison P p q).toHomotopy.trans (c1 P p q))
/-- Route and seed coordinates are independent. -/
def route : C(I × I, Carrier P p q) := (routeHomotopy P p q).toContinuousMap

theorem route_start (s : I) : route P p q (0, s) = start P p q s :=
  (routeHomotopy P p q).apply_zero s

theorem route_finish (s : I) : route P p q (1, s) = finish P p q s :=
  (routeHomotopy P p q).apply_one s

theorem c0_bottom (r : I) : c0 P p q (r, 0) = minusTip P p q := by
  change toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.face P
    p q (unitInterval.symm r, 0)) = _
  rw [CoefficientBassPositiveC0CarrierSeed.face_bottom]
  rfl

theorem c0_top (r : I) : c0 P p q (r, 1) = plusTip P p q := by
  change toJ0 P p q (CoefficientBassPositiveC0CarrierSeed.face P
    p q (unitInterval.symm r, 1)) = _
  rw [CoefficientBassPositiveC0CarrierSeed.face_top]
  rfl

theorem route_bottom (r : I) : route P p q (r, 0) = minusTip P p q := by
  change ((c0 P p q).trans ((reverseComparison P p q).toHomotopy.trans (c1 P p q))) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_bottom P p q _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact (reverseComparison P p q).source _
    · exact CoefficientBassPositiveC1SeedFace.face_bottom P p q _

theorem route_top (r : I) : route P p q (r, 1) = plusTip P p q := by
  change ((c0 P p q).trans ((reverseComparison P p q).toHomotopy.trans (c1 P p q))) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_top P p q _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact (reverseComparison P p q).target _
    · exact CoefficientBassPositiveC1SeedFace.face_top P p q _

/-- Exact supported-right recovery, with arbitrary degree and independent route/seed/input times. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (route P p q (r, s)) x =
      Path.toContinuousMap ((CoefficientBassCompositeMixedRoutes.supportedRight P p q).level n
        (r, x)) s := by
  let H0 := ((boundedFlatCoefficientCompositionHomotopy P p q).postcomp
    (boundedFlatCoefficientBassPositiveConeSeed P c)).symm
  let J := (boundedFlatCoefficientBassPositiveTransitionHomotopy P (p ≫ q)).symm
  let H1 := (Homotopy.precomp (boundedFlatCoefficientBassPositiveConeSeed P a)
    (CoefficientBassCompositeMixedRoutes.supportedComposition P p q)).cast rfl
      (Category.assoc _ _ _).symm
  change _ = Path.toContinuousMap ((H0.trans (J.trans H1)).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (c0 P p q)
    ((reverseComparison P p q).toHomotopy.trans (c1 P p q))
    (H0.levelHomotopy n).toHomotopy ((J.trans H1).levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    exact CoefficientBassPositiveC0CarrierSeedNative.face_native P p q n
      (unitInterval.symm t) s x
  · intro t
    refine ContinuousMap.Homotopy.Evaluation.trans_compare
      (reverseComparison P p q).toHomotopy (c1 P p q)
      (J.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
      (fun y ↦ CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) n y x)
      (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ t
    · intro v
      exact reverseComparison_transition P p q n v s x
    · intro v
      dsimp only [H1, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp,
        CoefficientBassCompositeMixedRoutes.supportedComposition]
      dsimp only [c1]
      have h := CoefficientBassPositiveC1SeedFaceNative.face_native P
        p q n v s x
      dsimp only [CoefficientBassPositiveC1SeedFaceNative.evaluate] at h
      dsimp only [polyRef, CoefficientBassCompositeJ0Polynomial.reference,
        chart, laurentRef, ordinary, shifted]
      exact h

end Quillen.PerfectComplexes.CoefficientBassCompositeActualRightRoute
