/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.EvaluationFactorExtraction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0RectangleNative

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0PositiveRailsNative
open CommonReferenceNerve CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0RectangleNative
private theorem carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : LoopPrespectrum.Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The entire minus source boundary word has its original native image. -/
theorem sourceMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (((positiveMovementMinus P p q).trans
        (polynomialMovementMinus
        P p q)) s) x =
      (((CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).path n x).trans
        ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).path n x)) s := by
  have h := rectangleMinus_positivePasting P p q n 0 s x
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) n ((rectangleMinus P p q).toFun (0, s)) x = _ at h
  rw [(rectangleMinus P p q).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- The entire minus target boundary word has its original native image. -/
theorem targetMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (((oldPositiveMinus P p q).symm.trans
        ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))) s) x =
      (((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm.trans
        (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
        ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))) s := by
  have h := rectangleMinus_positivePasting P p q n 1 s x
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) n ((rectangleMinus P p q).toFun (1, s)) x = _ at h
  rw [(rectangleMinus P p q).map_one_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- Every point of the minus positiveMovement rail has its original native value. -/
theorem positiveMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (positiveMovementMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((positiveMovementMinus P p q) s) = ((CoefficientBassPositiveNullTrack.positiveMovement
    P (arrow p q)).path n x) s
  exact Path.Evaluation.left_factor ev (positiveMovementMinus P p q) (polynomialMovementMinus P p q)
    ((CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).path n x)
    (fun t ↦ sourceMinus_native P p q n t x) s

/-- Every point of the minus oldPositive rail has its original native value. -/
theorem oldPositiveMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (oldPositiveMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((oldPositiveMinus P p q) s) = ((CoefficientBassPositiveNullTrack.oldPositive P
    (arrow p q)).path n x) s
  have h := Path.Evaluation.left_factor ev
    (oldPositiveMinus P p q).symm ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetMinus_native P p q n t x)
  exact Path.Evaluation.unreverse ev (oldPositiveMinus P p q)
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x) h s

/-- Every point of the minus laurentMovement rail has its original native value. -/
theorem laurentMovementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (laurentMovementMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((laurentMovementMinus P p q) s) = ((CoefficientBassPositiveNullTrack.laurentMovement P
    (arrow p q)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositiveMinus P p q).symm ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetMinus_native P p q n t x)
  exact Path.Evaluation.left_factor ev
    (laurentMovementMinus P p q) (newPositiveMinus P p q)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x) h s

/-- Every point of the minus newPositive rail has its original native value. -/
theorem newPositiveMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (newPositiveMinus P p q s) x =
      (CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((newPositiveMinus P p q) s) = ((CoefficientBassPositiveNullTrack.newPositive P
    (arrow p q)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositiveMinus P p q).symm ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetMinus_native P p q n t x)
  exact Path.Evaluation.right_factor ev
    (laurentMovementMinus P p q) (newPositiveMinus P p q)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x) h s

/-- The entire plus source boundary word has its original native image. -/
theorem sourcePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (((positiveMovementPlus P p q).trans
        (polynomialMovementPlus P p q)) s) x =
      (((CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).path n x).trans
        ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).path n x)) s := by
  have h := rectanglePlus_positivePasting P p q n 0 s x
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) n ((rectanglePlus P p q).toFun (0, s)) x = _ at h
  rw [(rectanglePlus P p q).map_zero_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n).apply_zero
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- The entire plus target boundary word has its original native image. -/
theorem targetPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (((oldPositivePlus P p q).symm.trans
        ((laurentMovementPlus P p q).trans (newPositivePlus P p q))) s) x =
      (((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm.trans
        (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
        ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))) s := by
  have h := rectanglePlus_positivePasting P p q n 1 s x
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) n ((rectanglePlus P p q).toFun (1, s)) x = _ at h
  rw [(rectanglePlus P p q).map_one_left s] at h
  have hb := ((CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n).apply_one
    (s, x)
  have he := h.trans hb
  simpa only [← LoopPrespectrum.Homotopy.path_trans,
    ← LoopPrespectrum.Homotopy.path_symm, native_path_apply, carrier_path_apply] using he

/-- Every point of the plus positiveMovement rail has its original native value. -/
theorem positiveMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (positiveMovementPlus P p q s) x =
      (CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((positiveMovementPlus P p q) s) = ((CoefficientBassPositiveNullTrack.positiveMovement P
    (arrow p q)).path n x) s
  exact Path.Evaluation.left_factor ev (positiveMovementPlus P p q) (polynomialMovementPlus P p q)
    ((CoefficientBassPositiveNullTrack.positiveMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).path n x)
    (fun t ↦ sourcePlus_native P p q n t x) s

/-- Every point of the plus oldPositive rail has its original native value. -/
theorem oldPositivePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (oldPositivePlus P p q s) x =
      (CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((oldPositivePlus P p q) s) = ((CoefficientBassPositiveNullTrack.oldPositive P (arrow
    p q)).path n x) s
  have h := Path.Evaluation.left_factor ev
    (oldPositivePlus P p q).symm ((laurentMovementPlus P p q).trans (newPositivePlus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetPlus_native P p q n t x)
  exact Path.Evaluation.unreverse ev (oldPositivePlus P p q)
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x) h s

/-- Every point of the plus laurentMovement rail has its original native value. -/
theorem laurentMovementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (laurentMovementPlus P p q s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((laurentMovementPlus P p q) s) = ((CoefficientBassPositiveNullTrack.laurentMovement P
    (arrow p q)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositivePlus P p q).symm ((laurentMovementPlus P p q).trans (newPositivePlus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetPlus_native P p q n t x)
  exact Path.Evaluation.left_factor ev
    (laurentMovementPlus P p q) (newPositivePlus P p q)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x) h s

/-- Every point of the plus newPositive rail has its original native value. -/
theorem newPositivePlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (newPositivePlus P p q s) x =
      (CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).level n (s, x) := by
  let ev := fun z : Carrier P p q ↦
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n z x
  change ev ((newPositivePlus P p q) s) = ((CoefficientBassPositiveNullTrack.newPositive P (arrow
    p q)).path n x) s
  have h := Path.Evaluation.right_factor ev
    (oldPositivePlus P p q).symm ((laurentMovementPlus P p q).trans (newPositivePlus P p q))
    ((CoefficientBassPositiveNullTrack.oldPositive P (arrow p q)).path n x).symm
    (((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x).trans
      ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x))
    (fun t ↦ targetPlus_native P p q n t x)
  exact Path.Evaluation.right_factor ev
    (laurentMovementPlus P p q) (newPositivePlus P p q)
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow p q)).path n x)
    ((CoefficientBassPositiveNullTrack.newPositive P (arrow p q)).path n x) h s

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0PositiveRailsNative
