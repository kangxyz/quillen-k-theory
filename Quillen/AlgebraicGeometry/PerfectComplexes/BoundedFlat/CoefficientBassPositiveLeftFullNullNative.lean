/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPositiveRailsNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeComparisonNative
public import Quillen.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation

/-!
# Original native values of both finite left-route null comparisons

The seven whole path images and the two actual primitive surfaces determine the complete
five-stage pasted null. The original endpoint casts preserve both independent coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftFullNullNative
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftRectangles
open CoefficientBassPositiveLeftPairedNull CoefficientBassPositiveLeftNativeFamilies
open CoefficientBassPositiveLeftRectangleNative CoefficientBassPositiveLeftPositiveRailsNative
open CoefficientBassPositiveLeftConeComparisonNative

private theorem trans_native {X : Type v} [TopologicalSpace X] {a b c : X}
    {E F : LoopPrespectrum.{u}} {f g k : E ⟶ F}
    (n : ℕ) (x : E.space n) (ev : X → F.space n)
    (p : Path a b) (q : Path b c)
    (H : Homotopy f g) (K : Homotopy g k)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete first five-stage word has its original native value on either sheet. -/
theorem first_pastedNull_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstPastedNull P p q e (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.pastedNullComparison P p q).level n
        (r, (s, x)) := by
  let ev : Carrier P p q → _ := fun z ↦ nativeValue P p q n z x
  unfold firstPastedNull CoefficientBassPositiveLeftNativePostcomp.pastedNullComparison
  exact NativeNullWordEvaluation.pastedPositiveNullWord n (x) ev
    (firstOldPositive P p q e)
    (firstPositiveMovement P p q e)
    (firstPolynomialMovement P p q e)
    (firstLaurentMovement P p q e)
    (firstNewPositive P p q e)
    (firstOldCone P p q e)
    (firstNewCone P p q e)
    (CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q)
    (CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q)
    (CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q)
    (CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q)
    (CoefficientBassPositiveLeftNativePostcomp.newPositive P p q)
    (CoefficientBassPositiveLeftNativePostcomp.oldCone P p q)
    (CoefficientBassPositiveLeftNativePostcomp.newCone P p q)
    (firstRectangle P p q e) (CoefficientBassPositiveLeftNativePostcomp.positivePasting P p q)
    (firstConeComparison P p q e) (CoefficientBassPositiveLeftNativePostcomp.conePasting P p q)
    (fun t ↦ first_oldPositive_native P p q e n t x)
    (fun t ↦ first_positiveMovement_native P p q e n t x)
    (fun t ↦ first_polynomialMovement_native P p q e n t x)
    (fun t ↦ first_laurentMovement_native P p q e n t x)
    (fun t ↦ first_newPositive_native P p q e n t x)
    (fun t ↦ first_oldCone_native P p q e n t x)
    (fun t ↦ first_newCone_native P p q e n t x)
    (fun r s ↦ first_rectangle_postcomp P p q e n r s x)
    (fun r s ↦ first_cone_native_wrapper P p q e n r s x) r s

/-- The original first null endpoint transports do not alter the whole comparison. -/
theorem first_originalNull_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstPastedNull P p q e (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.originalNullComparison P p q).level n
        (r, (s, x)) := by
  unfold CoefficientBassPositiveLeftNativePostcomp.originalNullComparison
  rw [Homotopy.RelHomotopy.ofLevels_apply]
  exact first_pastedNull_native P p q e n r s x

/-- The complete first new null keeps the original positive/cylinder half cut. -/
theorem first_newNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (firstNewNull P p q e s) x =
      (CoefficientBassPositiveLeftNativePostcomp.originalNewNull P p q).level n (s, x) := by
  rw [CoefficientBassPositiveLeftNativePostcomp.originalNewNull_level]
  exact trans_native n (x) (fun z ↦ nativeValue P p q n z x)
    (firstNewPositive P p q e) (firstNewCone P p q e)
    (CoefficientBassPositiveLeftNativePostcomp.newPositive P p q)
    (CoefficientBassPositiveLeftNativePostcomp.newCone P p q)
    (fun t ↦ first_newPositive_native P p q e n t x)
    (fun t ↦ first_newCone_native P p q e n t x) s

/-- The complete middle five-stage word has its original native value on either sheet. -/
theorem middle_pastedNull_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middlePastedNull P p q e (r, s)) x =
      (CoefficientBassPositiveNullTrack.pastedNullComparison P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev : Carrier P p q → _ := fun z ↦ nativeValue P p q n z x
  unfold middlePastedNull CoefficientBassPositiveNullTrack.pastedNullComparison
  unfold CoefficientBassPositiveNullTrack.straightPositivePasting
  exact NativeNullWordEvaluation.pastedPositiveNullWord n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) ev
    (middleOldPositive P p q e)
    (middlePositiveMovement P p q e)
    (middlePolynomialMovement P p q e)
    (middleLaurentMovement P p q e)
    (middleNewPositive P p q e)
    (middleOldCone P p q e)
    (middleNewCone P p q e)
    (CoefficientBassPositiveNullTrack.oldPositive P q)
    (CoefficientBassPositiveNullTrack.positiveMovement P q)
    (CoefficientBassPositiveNullTrack.polynomialMovement P q)
    (CoefficientBassPositiveNullTrack.laurentMovement P q)
    (CoefficientBassPositiveNullTrack.newPositive P q)
    (CoefficientBassPositiveNullTrack.oldCone P q)
    (CoefficientBassPositiveNullTrack.newCone P q)
    (middleRectangle P p q e) (CoefficientBassPositiveNullTrack.positivePasting P q)
    (middleConeComparison P p q e) (CoefficientBassPositiveNullTrack.conePasting P q)
    (fun t ↦ middle_oldPositive_native P p q e n t x)
    (fun t ↦ middle_positiveMovement_native P p q e n t x)
    (fun t ↦ middle_polynomialMovement_native P p q e n t x)
    (fun t ↦ middle_laurentMovement_native P p q e n t x)
    (fun t ↦ middle_newPositive_native P p q e n t x)
    (fun t ↦ middle_oldCone_native P p q e n t x)
    (fun t ↦ middle_newCone_native P p q e n t x)
    (fun r s ↦ middle_rectangle_native P p q e n r s x)
    (fun r s ↦ middle_cone_native P p q e n r s x) r s

/-- The original middle null endpoint transports do not alter the whole comparison. -/
theorem middle_originalNull_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middlePastedNull P p q e (r, s)) x =
      (CoefficientBassPositiveNullTrack.originalNullComparison P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  unfold CoefficientBassPositiveNullTrack.originalNullComparison
  rw [Homotopy.RelHomotopy.ofLevels_apply]
  exact middle_pastedNull_native P p q e n r s x

/-- The complete middle new null keeps the original positive/cylinder half cut. -/
theorem middle_newNull_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (middleNewNull P p q e s) x =
      (CoefficientBassPositiveNullTrack.originalNewNull P q).level n
        (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) := by
  rw [CoefficientBassPositiveNullTrack.originalNewNull_level]
  exact trans_native n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)
    (fun z ↦ nativeValue P p q n z x)
    (middleNewPositive P p q e) (middleNewCone P p q e)
    (CoefficientBassPositiveNullTrack.newPositive P q)
    (CoefficientBassPositiveNullTrack.newCone P q)
    (fun t ↦ middle_newPositive_native P p q e n t x)
    (fun t ↦ middle_newCone_native P p q e n t x) s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftFullNullNative
