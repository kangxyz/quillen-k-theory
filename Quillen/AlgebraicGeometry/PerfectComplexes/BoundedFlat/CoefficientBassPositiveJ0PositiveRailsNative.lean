/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0RectangleNative

/-!
# Whole positive rails recovered from the original full rectangle

Factor extraction uses exact half-interval substitutions, including the shared midpoint.
Both sheets retain their own carrier points; their common native images do not identify tips.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PositiveRailsNative
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0RectangleNative
private theorem carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : LoopPrespectrum.Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The entire minus source boundary word has its original native image. -/
theorem sourceMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (((positiveMovementMinus P d).trans (polynomialMovementMinus
        P d)) s) x =
      (((CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).path n x).trans
        ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).path n x)) s := by
  have h := rectangleMinus_positivePasting P d n 0 s x
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) n ((rectangleMinus P d).toFun (0, s)) x = _ at h
  rw [(rectangleMinus P d).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow d)).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- The entire minus target boundary word has its original native image. -/
theorem targetMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (((oldPositiveMinus P d).symm.trans ((laurentMovementMinus P
        d).trans (newPositiveMinus P d))) s) x =
      (((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm.trans
        (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
        ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))) s := by
  have h := rectangleMinus_positivePasting P d n 1 s x
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) n ((rectangleMinus P d).toFun (1, s)) x = _ at h
  rw [(rectangleMinus P d).map_one_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow d)).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- Every point of the minus positiveMovement rail has its original native value. -/
theorem positiveMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (positiveMovementMinus P d s) x =
      (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((positiveMovementMinus P d) s) = ((CoefficientBassPositiveNullTrack.positiveMovement
    P (arrow d)).path n x) s
  exact Path.Evaluation.left_factor ev (positiveMovementMinus P d) (polynomialMovementMinus P d)
    ((CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).path n x)
    (fun t ↦ sourceMinus_native P d n t x) s

/-- Every point of the minus oldPositive rail has its original native value. -/
theorem oldPositiveMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldPositiveMinus P d s) x =
      (CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((oldPositiveMinus P d) s) = ((CoefficientBassPositiveNullTrack.oldPositive P (arrow
    d)).path n x) s
  have h := Path.Evaluation.left_factor ev
    (oldPositiveMinus P d).symm ((laurentMovementMinus P d).trans (newPositiveMinus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetMinus_native P d n t x)
  exact Path.Evaluation.unreverse ev (oldPositiveMinus P d)
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x) h s

/-- Every point of the minus laurentMovement rail has its original native value. -/
theorem laurentMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (laurentMovementMinus P d s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((laurentMovementMinus P d) s) = ((CoefficientBassPositiveNullTrack.laurentMovement P
    (arrow d)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositiveMinus P d).symm ((laurentMovementMinus P d).trans (newPositiveMinus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetMinus_native P d n t x)
  exact Path.Evaluation.left_factor ev
    (laurentMovementMinus P d) (newPositiveMinus P d)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x) h s

/-- Every point of the minus newPositive rail has its original native value. -/
theorem newPositiveMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newPositiveMinus P d s) x =
      (CoefficientBassPositiveNullTrack.newPositive P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((newPositiveMinus P d) s) = ((CoefficientBassPositiveNullTrack.newPositive P (arrow
    d)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositiveMinus P d).symm ((laurentMovementMinus P d).trans (newPositiveMinus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetMinus_native P d n t x)
  exact Path.Evaluation.right_factor ev
    (laurentMovementMinus P d) (newPositiveMinus P d)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x) h s

/-- The entire plus source boundary word has its original native image. -/
theorem sourcePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (((positiveMovementPlus P d).trans (polynomialMovementPlus P
        d)) s) x =
      (((CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).path n x).trans
        ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).path n x)) s := by
  have h := rectanglePlus_positivePasting P d n 0 s x
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) n ((rectanglePlus P d).toFun (0, s)) x = _ at h
  rw [(rectanglePlus P d).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow d)).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- The entire plus target boundary word has its original native image. -/
theorem targetPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (((oldPositivePlus P d).symm.trans ((laurentMovementPlus P
        d).trans (newPositivePlus P d))) s) x =
      (((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm.trans
        (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
        ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))) s := by
  have h := rectanglePlus_positivePasting P d n 1 s x
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d) n ((rectanglePlus P d).toFun (1, s)) x = _ at h
  rw [(rectanglePlus P d).map_one_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow d)).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- Every point of the plus positiveMovement rail has its original native value. -/
theorem positiveMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (positiveMovementPlus P d s) x =
      (CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((positiveMovementPlus P d) s) = ((CoefficientBassPositiveNullTrack.positiveMovement P
    (arrow d)).path n x) s
  exact Path.Evaluation.left_factor ev (positiveMovementPlus P d) (polynomialMovementPlus P d)
    ((CoefficientBassPositiveNullTrack.positiveMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).path n x)
    (fun t ↦ sourcePlus_native P d n t x) s

/-- Every point of the plus oldPositive rail has its original native value. -/
theorem oldPositivePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldPositivePlus P d s) x =
      (CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((oldPositivePlus P d) s) = ((CoefficientBassPositiveNullTrack.oldPositive P (arrow
    d)).path n x) s
  have h := Path.Evaluation.left_factor ev
    (oldPositivePlus P d).symm ((laurentMovementPlus P d).trans (newPositivePlus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetPlus_native P d n t x)
  exact Path.Evaluation.unreverse ev (oldPositivePlus P d)
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x) h s

/-- Every point of the plus laurentMovement rail has its original native value. -/
theorem laurentMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (laurentMovementPlus P d s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((laurentMovementPlus P d) s) = ((CoefficientBassPositiveNullTrack.laurentMovement P
    (arrow d)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositivePlus P d).symm ((laurentMovementPlus P d).trans (newPositivePlus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetPlus_native P d n t x)
  exact Path.Evaluation.left_factor ev
    (laurentMovementPlus P d) (newPositivePlus P d)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x) h s

/-- Every point of the plus newPositive rail has its original native value. -/
theorem newPositivePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newPositivePlus P d s) x =
      (CoefficientBassPositiveNullTrack.newPositive P (arrow d)).level n (s, x) := by
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  change ev ((newPositivePlus P d) s) = ((CoefficientBassPositiveNullTrack.newPositive P (arrow
    d)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositivePlus P d).symm ((laurentMovementPlus P d).trans (newPositivePlus P d))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow d)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x))
    (fun t ↦ targetPlus_native P d n t x)
  exact Path.Evaluation.right_factor ev
    (laurentMovementPlus P d) (newPositivePlus P d)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow d)).path n x) h s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PositiveRailsNative
