/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftUnitNative

/-! The four complete typed unit rails recovered from their unchanged native unit pastings. -/
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

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitRailsNative
open CommonReferenceNerve CoefficientBassPositiveC0CarrierSeed
open CoefficientBassPositiveLeftRectangles CoefficientBassPositiveLeftUnitPasting
open CoefficientBassPositiveLeftNativeFamilies CoefficientBassPositiveLeftUnitNative

private theorem carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete first unit source word has the exact original native value. -/
theorem first_unit_source_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((firstOldUnit P p q).trans (firstLaurentMovement P p q true)) s) x =
      (((CoefficientBassPositiveLeftNativePostcomp.oldUnit P p q).path n x).trans
        ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x)) s := by
  have h := first_unit_postcomp P p q n 0 s x
  change nativeValue P p q n ((firstUnitComparison P p q).toFun (0, s)) x = _ at h
  rw [(firstUnitComparison P p q).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveLeftNativePostcomp.unitPasting P p q).level n).apply_zero (s,
    x)
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, native_path_apply, carrier_path_apply] using he

/-- Every point of the typed first oldUnit retains its original native value. -/
theorem first_oldUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstOldUnit P p q) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.oldUnit P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstOldUnit P p q) s) = ((CoefficientBassPositiveLeftNativePostcomp.oldUnit P p
    q).path n x) s
  exact Path.Evaluation.left_factor ev (firstOldUnit P p q) (firstLaurentMovement P p q true)
    ((CoefficientBassPositiveLeftNativePostcomp.oldUnit P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x) (fun t ↦
      first_unit_source_native P p q n t x) s

/-- The complete first unit target word has the exact original native value. -/
theorem first_unit_target_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((firstLaurentMovement P p q false).trans (firstNewUnit P p q)) s) x =
      (((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x).trans
        ((CoefficientBassPositiveLeftNativePostcomp.newUnit P p q).path n x)) s := by
  have h := first_unit_postcomp P p q n 1 s x
  change nativeValue P p q n ((firstUnitComparison P p q).toFun (1, s)) x = _ at h
  rw [(firstUnitComparison P p q).map_one_left s] at h
  have hb := ((CoefficientBassPositiveLeftNativePostcomp.unitPasting P p q).level n).apply_one (s,
    x)
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, native_path_apply, carrier_path_apply] using he

/-- Every point of the typed first newUnit retains its original native value. -/
theorem first_newUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstNewUnit P p q) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.newUnit P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstNewUnit P p q) s) = ((CoefficientBassPositiveLeftNativePostcomp.newUnit P p
    q).path n x) s
  exact Path.Evaluation.right_factor ev (firstLaurentMovement P p q false) (firstNewUnit P p q)
    ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.newUnit P p q).path n x) (fun t ↦
      first_unit_target_native P p q n t x) s

/-- The complete middle unit source word has the exact original native value. -/
theorem middle_unit_source_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((middleOldUnit P p q).trans (middleLaurentMovement P p q true)) s) x =
      (((CoefficientBassPositiveTransitionTrack.oldUnit P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
        ((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))) s := by
  have h := middle_unit_native P p q n 0 s x
  change nativeValue P p q n ((middleUnitComparison P p q).toFun (0, s)) x = _ at h
  rw [(middleUnitComparison P p q).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveTransitionTrack.unitPasting P q).level n).apply_zero (s,
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, native_path_apply, carrier_path_apply] using he

/-- Every point of the typed middle oldUnit retains its original native value. -/
theorem middle_oldUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middleOldUnit P p q) s) x =
      (CoefficientBassPositiveTransitionTrack.oldUnit P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middleOldUnit P p q) s) = ((CoefficientBassPositiveTransitionTrack.oldUnit P q).path n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  exact Path.Evaluation.left_factor ev (middleOldUnit P p q) (middleLaurentMovement P p q true)
    ((CoefficientBassPositiveTransitionTrack.oldUnit P q).path n ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P p)).map n x)) ((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) (fun t ↦
      middle_unit_source_native P p q n t x) s

/-- The complete middle unit target word has the exact original native value. -/
theorem middle_unit_target_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((middleLaurentMovement P p q false).trans (middleNewUnit P p q)) s) x =
      (((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).trans
        ((CoefficientBassPositiveTransitionTrack.newUnit P q).path n
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))) s := by
  have h := middle_unit_native P p q n 1 s x
  change nativeValue P p q n ((middleUnitComparison P p q).toFun (1, s)) x = _ at h
  rw [(middleUnitComparison P p q).map_one_left s] at h
  have hb := ((CoefficientBassPositiveTransitionTrack.unitPasting P q).level n).apply_one (s,
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, native_path_apply, carrier_path_apply] using he

/-- Every point of the typed middle newUnit retains its original native value. -/
theorem middle_newUnit_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((middleNewUnit P p q) s) x =
      (CoefficientBassPositiveTransitionTrack.newUnit P q).level n (s,
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((middleNewUnit P p q) s) = ((CoefficientBassPositiveTransitionTrack.newUnit P q).path n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) s
  exact Path.Evaluation.right_factor ev (middleLaurentMovement P p q false) (middleNewUnit P p q)
    ((CoefficientBassPositiveNullTrack.laurentMovement P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
      ((CoefficientBassPositiveTransitionTrack.newUnit P q).path n
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) (fun t ↦
      middle_unit_target_native P p q n t x) s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftUnitRailsNative
