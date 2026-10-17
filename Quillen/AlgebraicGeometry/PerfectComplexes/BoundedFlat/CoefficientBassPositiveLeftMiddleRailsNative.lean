/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftRectangleNative

/-! Whole middle rectangle rails, recovered by exact path factor extraction on both sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftPositiveRailsNative
open CommonReferenceNerve CoefficientBassPositiveC0CarrierSeed
open CoefficientBassPositiveLeftRectangles CoefficientBassPositiveLeftRectangleNative
open CoefficientBassPositiveLeftNativeFamilies

private theorem middle_carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem middle_native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete middle source boundary retains its original native concatenation. -/
theorem middle_source_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((middlePositiveMovement P p q e).trans (middlePolynomialMovement P p q e))
      s) x =
      (((CoefficientBassPositiveNullTrack.positiveMovement P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
        ((CoefficientBassPositiveNullTrack.polynomialMovement P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))) s := by
  have h := middle_rectangle_native P p q e n 0 s x
  change nativeValue P p q n ((middleRectangle P p q e).toFun (0, s)) x = _ at h
  rw [(middleRectangle P p q e).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P q).level n).apply_zero (s,
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, ← Homotopy.path_symm,
    middle_native_path_apply, middle_carrier_path_apply] using he

/-- The complete middle target boundary retains its original native nested word. -/
theorem middle_target_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((middleOldPositive P p q e).symm.trans
        ((middleLaurentMovement P p q e).trans (middleNewPositive P p q e))) s) x =
      (((CoefficientBassPositiveNullTrack.oldPositive P q).path n ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P p)).map n x)).symm.trans
        (((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
          ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
          ((CoefficientBassPositiveNullTrack.newPositive P q).path n
          ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)))) s := by
  have h := middle_rectangle_native P p q e n 1 s x
  change nativeValue P p q n ((middleRectangle P p q e).toFun (1, s)) x = _ at h
  rw [(middleRectangle P p q e).map_one_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P q).level n).apply_one (s,
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, ← Homotopy.path_symm,
    middle_native_path_apply, middle_carrier_path_apply] using he

/-- Every middle oldPositive point has its exact native value, on either sheet. -/
theorem middle_oldPositive_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middleOldPositive P p q e) s) x =
      (CoefficientBassPositiveNullTrack.oldPositive P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middleOldPositive P p q e) s) = ((CoefficientBassPositiveNullTrack.oldPositive P
    q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  have h := Path.Evaluation.left_factor ev
    (middleOldPositive P p q e).symm ((middleLaurentMovement P p q e).trans (middleNewPositive P p q
      e))
    ((CoefficientBassPositiveNullTrack.oldPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)).symm (((CoefficientBassPositiveNullTrack.laurentMovement P
      q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
      ((CoefficientBassPositiveNullTrack.newPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)))
    (fun t ↦ middle_target_native P p q e n t x)
  exact Path.Evaluation.unreverse ev (middleOldPositive P p q e)
    ((CoefficientBassPositiveNullTrack.oldPositive P q).path n ((boundedFlatPerfectPrespectrumMap
    (coefficientMap P p)).map n x)) h s

/-- Every middle positiveMovement point has its exact native value, on either sheet. -/
theorem middle_positiveMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middlePositiveMovement P p q e) s) x =
      (CoefficientBassPositiveNullTrack.positiveMovement P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middlePositiveMovement P p q e) s) =
    ((CoefficientBassPositiveNullTrack.positiveMovement P q).path n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  exact Path.Evaluation.left_factor ev
    (middlePositiveMovement P p q e) (middlePolynomialMovement P p q e)
    ((CoefficientBassPositiveNullTrack.positiveMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
      ((CoefficientBassPositiveNullTrack.polynomialMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
    (fun t ↦ middle_source_native P p q e n t x) s

/-- Every middle polynomialMovement point has its exact native value, on either sheet. -/
theorem middle_polynomialMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middlePolynomialMovement P p q e) s) x =
      (CoefficientBassPositiveNullTrack.polynomialMovement P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middlePolynomialMovement P p q e) s) =
    ((CoefficientBassPositiveNullTrack.polynomialMovement P q).path n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  exact Path.Evaluation.right_factor ev
    (middlePositiveMovement P p q e) (middlePolynomialMovement P p q e)
    ((CoefficientBassPositiveNullTrack.positiveMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
      ((CoefficientBassPositiveNullTrack.polynomialMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
    (fun t ↦ middle_source_native P p q e n t x) s

/-- Every middle laurentMovement point has its exact native value, on either sheet. -/
theorem middle_laurentMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middleLaurentMovement P p q e) s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middleLaurentMovement P p q e) s) = ((CoefficientBassPositiveNullTrack.laurentMovement
    P q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  have h := Path.Evaluation.right_factor ev
    (middleOldPositive P p q e).symm ((middleLaurentMovement P p q e).trans (middleNewPositive P p q
      e))
    ((CoefficientBassPositiveNullTrack.oldPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)).symm (((CoefficientBassPositiveNullTrack.laurentMovement P
      q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
      ((CoefficientBassPositiveNullTrack.newPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)))
    (fun t ↦ middle_target_native P p q e n t x)
  exact Path.Evaluation.left_factor ev
    (middleLaurentMovement P p q e) (middleNewPositive P p q e)
    ((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
      ((CoefficientBassPositiveNullTrack.newPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)) h s

/-- Every middle newPositive point has its exact native value, on either sheet. -/
theorem middle_newPositive_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middleNewPositive P p q e) s) x =
      (CoefficientBassPositiveNullTrack.newPositive P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middleNewPositive P p q e) s) = ((CoefficientBassPositiveNullTrack.newPositive P
    q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  have h := Path.Evaluation.right_factor ev
    (middleOldPositive P p q e).symm ((middleLaurentMovement P p q e).trans (middleNewPositive P p q
      e))
    ((CoefficientBassPositiveNullTrack.oldPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)).symm (((CoefficientBassPositiveNullTrack.laurentMovement P
      q).path n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
      ((CoefficientBassPositiveNullTrack.newPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)))
    (fun t ↦ middle_target_native P p q e n t x)
  exact Path.Evaluation.right_factor ev
    (middleLaurentMovement P p q e) (middleNewPositive P p q e)
    ((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
      ((CoefficientBassPositiveNullTrack.newPositive P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)) h s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPositiveRailsNative
