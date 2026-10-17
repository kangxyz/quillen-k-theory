/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualRightRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0C0SeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1WholeOldSeedSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFaceLoopFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveMixedRoutes

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeActualLeftRoute
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeCarrierReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSeedReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeC0CarrierSeedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeC1CarrierSeedNative

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
namespace Quillen.PerfectComplexes.CoefficientBassNegativeActualRightRoute
open CommonReferenceNerve CoefficientBassNegativeActualLeftRoute
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Equality of the actual composite arrows, before any native evaluation. -/
theorem composite_eq : pArrow d ≫ (underToLaurent R).app d = pArrow d ≫ qArrow d :=
  (polynomialUnderCoefficient_toLaurent R d).trans
    (polynomialUnderCoefficient_toLaurentInvert R d).symm

/-- Full carrier transport retains both reference isomorphisms and the forward inner unit. -/
def transport : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    (pArrow d) ((underToLaurent R).app d), Carrier P d) :=
  CoefficientBassNegativeCarrierReference.transport P (pArrow d) ((underToLaurent R).app d)
    (pArrow d) (qArrow d) (composite_eq d)

/-- The transported new J0 conjugate word, joining the two carrier tips. -/
def targetWord : C(I, Carrier P d) :=
  ⟨fun s ↦ transport P d (CoefficientBassPositiveJ0Conjugation.targetWord P d s),
    by fun_prop⟩

/-- The transported old J0 conjugate word, joining the two carrier tips. -/
def sourceWord : C(I, Carrier P d) :=
  ⟨fun s ↦ transport P d (CoefficientBassPositiveJ0Conjugation.sourceWord P d s),
    by fun_prop⟩

theorem targetWord_apply (s : I) : targetWord P d s =
    transport P d (CoefficientBassPositiveJ0Conjugation.targetWord P d s) := by
  dsimp only [targetWord, ContinuousMap.coe_mk]

theorem sourceWord_apply (s : I) : sourceWord P d s =
    transport P d (CoefficientBassPositiveJ0Conjugation.sourceWord P d s) := by
  dsimp only [sourceWord, ContinuousMap.coe_mk]

/-- The old positive J0 geometry is transported through equality of all carrier data. -/
def j0 : (targetWord P d).Homotopy (sourceWord P d) where
  toFun z := transport P d (CoefficientBassPositiveJ0Conjugation.reverseComparison P d z)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    have h := congrArg (transport P d)
      ((CoefficientBassPositiveJ0Conjugation.reverseComparison P d).apply_zero s)
    exact h.trans (targetWord_apply P d s).symm
  map_one_left s := by
    have h := congrArg (transport P d)
      ((CoefficientBassPositiveJ0Conjugation.reverseComparison P d).apply_one s)
    exact h.trans (sourceWord_apply P d s).symm

/-- The complete source C0 word agrees pointwise before forming a homotopy record. -/
theorem c0_source_word (s : I) :
    CoefficientBassPositiveC0CarrierSeed.face P (pArrow d) (qArrow d) (0, s) =
      transport P d (CoefficientBassPositiveJ0Conjugation.targetWord P d s) := by
  have h0 := CoefficientBassNegativeSeedReference.c0_source_heq P (pArrow d)
    ((underToLaurent R).app d) (pArrow d) (qArrow d) (composite_eq d) s
  have hp := (CoefficientBassPositiveActualRightRoute.c0 P d).apply_one s
  dsimp only [CoefficientBassPositiveActualRightRoute.c0,
    CoefficientBassPositiveJ0C0SeedAlignment.toJ0,
    CoefficientBassPositiveC0CarrierSeed.reversedFace] at hp
  change CoefficientBassPositiveC0CarrierSeed.face P (pArrow d)
    ((underToLaurent R).app d) (unitInterval.symm 1, s) =
      CoefficientBassPositiveJ0Conjugation.targetWord P d s at hp
  rw [unitInterval.symm_one] at hp
  have ht := CoefficientBassNegativeCarrierReference.transport_heq P (pArrow d)
    ((underToLaurent R).app d) (pArrow d) (qArrow d) (composite_eq d)
    (CoefficientBassPositiveJ0Conjugation.targetWord P d s)
  dsimp only [CoefficientBassPositiveJ0ConeBoundaries.firstArrow,
    CoefficientBassPositiveJ0ConeBoundaries.secondArrow, pArrow, qArrow, transport] at h0 hp ht ⊢
  exact eq_of_heq (h0.symm.trans ((heq_of_eq hp).trans ht.symm))

/-- The complete source C1 word agrees pointwise before forming a homotopy record. -/
theorem c1_source_word (s : I) :
    CoefficientBassPositiveC1SeedFace.face P (pArrow d) (qArrow d) (0, s) =
      transport P d (CoefficientBassPositiveJ0Conjugation.sourceWord P d s) := by
  have h0 := CoefficientBassNegativeSeedReference.c1_source P (pArrow d)
    ((underToLaurent R).app d) (pArrow d) (qArrow d) (composite_eq d) s
  have hp := (CoefficientBassPositiveActualRightRoute.c1 P d).apply_zero s
  dsimp only [CoefficientBassPositiveActualRightRoute.c1] at hp
  have h1 := congrArg (transport P d) hp
  dsimp only [CoefficientBassPositiveJ0ConeBoundaries.firstArrow,
    CoefficientBassPositiveJ0ConeBoundaries.secondArrow, pArrow, qArrow] at h0 h1 ⊢
  exact h0.symm.trans h1

/-- Negative C0 has its own actual coefficient-inverse specialization. -/
def c0 : (start P d).Homotopy (targetWord P d) where
  toFun z := CoefficientBassPositiveC0CarrierSeed.reversedFace P
    (pArrow d) (qArrow d) z
  continuous_toFun := by fun_prop
  map_zero_left s :=
    CoefficientBassPositiveC0CarrierSeed.reversedFace_source P
    (pArrow d) (qArrow d) s
  map_one_left s := by
    change CoefficientBassPositiveC0CarrierSeed.face P (pArrow d)
      (qArrow d) (unitInterval.symm 1, s) = _
    rw [unitInterval.symm_one]
    exact (c0_source_word P d s).trans (targetWord_apply P d s).symm

/-- The whole old-seed join is transported before entering the negative C1 square. -/
def c1 : (sourceWord P d).Homotopy (finish P d) where
  toFun z := CoefficientBassPositiveC1SeedFace.face P (pArrow d) (qArrow d) z
  continuous_toFun := by fun_prop
  map_zero_left s := by
    exact (c1_source_word P d s).trans (sourceWord_apply P d s).symm
  map_one_left _ := rfl

/-- Original route time: C0 on the first half, J0 on the next quarter, C1 on the last quarter. -/
def routeHomotopy : (start P d).Homotopy (finish P d) :=
  (c0 P d).trans ((j0 P d).trans (c1 P d))
/-- Route and seed coordinates are independent. -/
def route : C(I × I, Carrier P d) := (routeHomotopy P d).toContinuousMap

theorem route_start (s : I) : route P d (0, s) = start P d s :=
  (routeHomotopy P d).apply_zero s

theorem route_finish (s : I) : route P d (1, s) = finish P d s :=
  (routeHomotopy P d).apply_one s

theorem c0_bottom (r : I) : c0 P d (r, 0) = minusTip P d := by
  change (CoefficientBassPositiveC0CarrierSeed.face P
    (pArrow d) (qArrow d) (unitInterval.symm r, 0)) = _
  exact CoefficientBassPositiveC0CarrierSeed.face_bottom P
    (pArrow d) (qArrow d) _

theorem c0_top (r : I) : c0 P d (r, 1) = plusTip P d := by
  change (CoefficientBassPositiveC0CarrierSeed.face P
    (pArrow d) (qArrow d) (unitInterval.symm r, 1)) = _
  exact CoefficientBassPositiveC0CarrierSeed.face_top P (pArrow
    d) (qArrow d) _

/-- Pointwise map evaluation, kept independent of the native family. -/
theorem j0_apply (r s : I) : j0 P d (r, s) =
    transport P d (CoefficientBassPositiveJ0Conjugation.reverseComparison P d (r, s)) := by
  rfl

theorem j0_bottom (r : I) : j0 P d (r, 0) = minusTip P d := by
  rw [j0_apply]
  have h := congrArg (transport P d)
    ((CoefficientBassPositiveJ0Conjugation.reverseComparison P d).source r)
  have ht := CoefficientBassNegativeCarrierReference.transport_minusTip P
    (pArrow d) ((underToLaurent R).app d) (pArrow d) (qArrow d) (composite_eq d)
  dsimp only [transport, minusTip, polyRef, chart, laurentRef, ordinary, shifted,
    pArrow, qArrow, CoefficientBassPositiveJ0ConeBoundaries.polyRef,
    CoefficientBassPositiveJ0ConeBoundaries.chart,
    CoefficientBassPositiveJ0ConeBoundaries.laurentRef,
    CoefficientBassPositiveJ0ConeBoundaries.ordinary,
    CoefficientBassPositiveJ0ConeBoundaries.shifted,
    CoefficientBassPositiveJ0ConeBoundaries.firstArrow,
    CoefficientBassPositiveJ0ConeBoundaries.secondArrow,
    CoefficientBassPositiveJ0PolynomialMovement.reference] at h ht ⊢
  exact h.trans ht

theorem j0_top (r : I) : j0 P d (r, 1) = plusTip P d := by
  rw [j0_apply]
  have h := congrArg (transport P d)
    ((CoefficientBassPositiveJ0Conjugation.reverseComparison P d).target r)
  have ht := CoefficientBassNegativeCarrierReference.transport_plusTip P
    (pArrow d) ((underToLaurent R).app d) (pArrow d) (qArrow d) (composite_eq d)
  dsimp only [transport, plusTip, polyRef, chart, laurentRef, ordinary, shifted,
    pArrow, qArrow, CoefficientBassPositiveJ0ConeBoundaries.polyRef,
    CoefficientBassPositiveJ0ConeBoundaries.chart,
    CoefficientBassPositiveJ0ConeBoundaries.laurentRef,
    CoefficientBassPositiveJ0ConeBoundaries.ordinary,
    CoefficientBassPositiveJ0ConeBoundaries.shifted,
    CoefficientBassPositiveJ0ConeBoundaries.firstArrow,
    CoefficientBassPositiveJ0ConeBoundaries.secondArrow,
    CoefficientBassPositiveJ0PolynomialMovement.reference] at h ht ⊢
  exact h.trans ht

theorem route_bottom (r : I) : route P d (r, 0) = minusTip P d := by
  change ((c0 P d).trans ((j0 P d).trans (c1 P d))) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_bottom P d _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact j0_bottom P d _
    · exact CoefficientBassPositiveC1SeedFace.face_bottom P (pArrow d) (qArrow d) _

theorem route_top (r : I) : route P d (r, 1) = plusTip P d := by
  change ((c0 P d).trans ((j0 P d).trans (c1 P d))) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact c0_top P d _
  · rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact j0_top P d _
    · exact CoefficientBassPositiveC1SeedFace.face_top P (pArrow d) (qArrow d) _

/-- The transported J0 value preserves the literal common Laurent transition. -/
theorem j0_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (j0 P d (r, s)) x =
      Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P
          ((laurentUnderCoefficient R).app d)).symm.level n (r, x)) s := by
  have ht := CoefficientBassNegativeCarrierReference.transport_native P
    (pArrow d) ((underToLaurent R).app d) (pArrow d) (qArrow d)
    (composite_eq d) n (CoefficientBassPositiveJ0Conjugation.reverseComparison P d (r, s)) x
  have hj := CoefficientBassPositiveJ0Conjugation.reverseComparison_transition P d n r s x
  rw [j0_apply]
  dsimp only [transport]
  dsimp only [CoefficientBassPositiveJ0ConeBoundaries.polyRef,
    CoefficientBassPositiveJ0ConeBoundaries.laurentRef,
    CoefficientBassPositiveJ0ConeBoundaries.chart,
    CoefficientBassPositiveJ0ConeBoundaries.ordinary,
    CoefficientBassPositiveJ0ConeBoundaries.shifted,
    CoefficientBassPositiveJ0ConeBoundaries.firstArrow,
    CoefficientBassPositiveJ0ConeBoundaries.secondArrow,
    CoefficientBassPositiveJ0ConeBoundaries.arrow,
    CoefficientBassPositiveJ0PolynomialMovement.reference,
    CoefficientBassPositiveJ0PolynomialMovement.arrow] at hj
  dsimp only [polyRef, chart, laurentRef, ordinary, shifted, pArrow, qArrow] at ht ⊢
  exact ht.trans hj

/-- Exact supported-right recovery, with arbitrary degree and independent route/seed/input times. -/
theorem route_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (route P d (r, s)) x =
      Path.toContinuousMap ((CoefficientBassNegativeMixedRoutes.supportedRight P d).level n
        (r, x)) s := by
  let H0 := ((boundedFlatCoefficientLaurentMinusHomotopy P d).postcomp
    (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d))).symm
  let J := (boundedFlatCoefficientBassPositiveTransitionHomotopy P
    ((laurentUnderCoefficient R).app d)).symm
  let H1 := (Homotopy.precomp (boundedFlatCoefficientBassPositiveConeSeed P d)
    (CoefficientBassNegativeMixedRoutes.supportedComposition P d)).cast rfl
      (Category.assoc _ _ _).symm
  change _ = Path.toContinuousMap ((H0.trans (J.trans H1)).level n (r, x)) s
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (c0 P d)
    ((j0 P d).trans (c1 P d))
    (H0.levelHomotopy n).toHomotopy ((J.trans H1).levelHomotopy n).toHomotopy
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n y x)
    (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ r
  · intro t
    exact CoefficientBassNegativeC0CarrierSeedNative.actual_original_C0 P d n t s x
  · intro t
    refine ContinuousMap.Homotopy.Evaluation.trans_compare (j0 P d) (c1 P d)
      (J.levelHomotopy n).toHomotopy (H1.levelHomotopy n).toHomotopy
      (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
        (ordinary P d) (shifted P d) n y x)
      (fun y ↦ Path.toContinuousMap y s) s x ?_ ?_ t
    · intro v
      exact j0_native P d n v s x
    · intro v
      dsimp only [H1, Homotopy.levelHomotopy, Homotopy.cast, Homotopy.precomp, c1]
      have h := CoefficientBassNegativeC1CarrierSeedNative.face_supported P d n v s x
      dsimp only [CoefficientBassPositiveC1SeedFaceNative.evaluate] at h
      dsimp only [polyRef, chart, laurentRef, ordinary, shifted, pArrow, qArrow]
      exact h

end Quillen.PerfectComplexes.CoefficientBassNegativeActualRightRoute
