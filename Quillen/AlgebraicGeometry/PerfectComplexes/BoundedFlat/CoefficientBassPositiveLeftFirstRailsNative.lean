/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftRectangleNative

/-! Whole first rectangle rails, recovered by exact path factor extraction on both sheets. -/
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

private theorem first_carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem first_native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete first source boundary retains its original native concatenation. -/
theorem first_source_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((firstPositiveMovement P p q e).trans (firstPolynomialMovement P p q e))
      s) x =
      (((CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q).path n x).trans
        ((CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q).path n x)) s := by
  have h := first_rectangle_postcomp P p q e n 0 s x
  change nativeValue P p q n ((firstRectangle P p q e).toFun (0, s)) x = _ at h
  rw [(firstRectangle P p q e).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveLeftNativePostcomp.positivePasting P p q).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, ← Homotopy.path_symm,
    first_native_path_apply, first_carrier_path_apply] using he

/-- The complete first target boundary retains its original native nested word. -/
theorem first_target_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (((firstOldPositive P p q e).symm.trans
        ((firstLaurentMovement P p q e).trans (firstNewPositive P p q e))) s) x =
      (((CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).path n x).symm.trans
        (((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x).trans
          ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x))) s := by
  have h := first_rectangle_postcomp P p q e n 1 s x
  change nativeValue P p q n ((firstRectangle P p q e).toFun (1, s)) x = _ at h
  rw [(firstRectangle P p q e).map_one_left s] at h
  have hb := ((CoefficientBassPositiveLeftNativePostcomp.positivePasting P p q).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← Homotopy.path_trans, ← Homotopy.path_symm,
    first_native_path_apply, first_carrier_path_apply] using he

/-- Every first oldPositive point has its exact native value, on either sheet. -/
theorem first_oldPositive_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstOldPositive P p q e) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstOldPositive P p q e) s) = ((CoefficientBassPositiveLeftNativePostcomp.oldPositive
    P p q).path n x) s
  have h := Path.Evaluation.left_factor ev
    (firstOldPositive P p q e).symm ((firstLaurentMovement P p q e).trans (firstNewPositive P p q
      e))
    ((CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).path n x).symm
      (((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x).trans
      ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x))
    (fun t ↦ first_target_native P p q e n t x)
  exact Path.Evaluation.unreverse ev (firstOldPositive P p q e)
    ((CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).path n x) h s

/-- Every first positiveMovement point has its exact native value, on either sheet. -/
theorem first_positiveMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstPositiveMovement P p q e) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstPositiveMovement P p q e) s) =
    ((CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q).path n x) s
  exact Path.Evaluation.left_factor ev
    (firstPositiveMovement P p q e) (firstPolynomialMovement P p q e)
    ((CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q).path n x)
    (fun t ↦ first_source_native P p q e n t x) s

/-- Every first polynomialMovement point has its exact native value, on either sheet. -/
theorem first_polynomialMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstPolynomialMovement P p q e) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstPolynomialMovement P p q e) s) =
    ((CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q).path n x) s
  exact Path.Evaluation.right_factor ev
    (firstPositiveMovement P p q e) (firstPolynomialMovement P p q e)
    ((CoefficientBassPositiveLeftNativePostcomp.positiveMovement P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.polynomialMovement P p q).path n x)
    (fun t ↦ first_source_native P p q e n t x) s

/-- Every first laurentMovement point has its exact native value, on either sheet. -/
theorem first_laurentMovement_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstLaurentMovement P p q e) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstLaurentMovement P p q e) s) =
    ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x) s
  have h := Path.Evaluation.right_factor ev
    (firstOldPositive P p q e).symm ((firstLaurentMovement P p q e).trans (firstNewPositive P p q
      e))
    ((CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).path n x).symm
      (((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x).trans
      ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x))
    (fun t ↦ first_target_native P p q e n t x)
  exact Path.Evaluation.left_factor ev
    (firstLaurentMovement P p q e) (firstNewPositive P p q e)
    ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x) h s

/-- Every first newPositive point has its exact native value, on either sheet. -/
theorem first_newPositive_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n ((firstNewPositive P p q e) s) x =
      (CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦ nativeValue P p q n z x
  change ev ((firstNewPositive P p q e) s) = ((CoefficientBassPositiveLeftNativePostcomp.newPositive
    P p q).path n x) s
  have h := Path.Evaluation.right_factor ev
    (firstOldPositive P p q e).symm ((firstLaurentMovement P p q e).trans (firstNewPositive P p q
      e))
    ((CoefficientBassPositiveLeftNativePostcomp.oldPositive P p q).path n x).symm
      (((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x).trans
      ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x))
    (fun t ↦ first_target_native P p q e n t x)
  exact Path.Evaluation.right_factor ev
    (firstLaurentMovement P p q e) (firstNewPositive P p q e)
    ((CoefficientBassPositiveLeftNativePostcomp.laurentMovement P p q).path n x)
      ((CoefficientBassPositiveLeftNativePostcomp.newPositive P p q).path n x) h s

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPositiveRailsNative
