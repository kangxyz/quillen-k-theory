/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluationCells
public import Quillen.Topology.Prespectrum.NativeMovingSquareCells

/-! The original identical-leg moving square in the full four-edge reference tree. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier Quillen.NativePathCells Quillen.ScalarRectangle

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)
  (P : C(I × I, |parameterSSet (E ≫ J)|)) (L : C(I, |parameterSSet E|))

/-- The polynomial square in the first, distinct chart. -/
def movingPlus : C(I × I, space E J) :=
  (SSet.toTop.map (plusVertex E J)).hom.comp P

/-- The genuine overlap keeps its two independent coordinates. -/
def movingMiddle : C(I × I, space E J) :=
  (overlap E J).comp ⟨fun z ↦ (L z.1, z.2), by fun_prop⟩

/-- The second chart uses the original reversed polynomial path. -/
def movingMinus : C(I × I, space E J) :=
  (SSet.toTop.map (minusVertex E J)).hom.comp
    (P.comp ⟨fun z ↦ (z.1, unitInterval.symm z.2), by fun_prop⟩)

variable (h : ∀ r : I, P (r, 1) = SSet.toTop.map (attachment E J) (L r))

include h in
theorem moving_plus_seam (r : I) :
    movingPlus E J P (r, 1) = movingMiddle E J L (r, 0) := by
  change SSet.toTop.map (plusVertex E J) (P (r, 1)) = overlap E J (L r, 0)
  rw [h r, overlap_zero]

include h in
theorem moving_minus_seam (r : I) :
    movingMiddle E J L (r, 1) = movingMinus E J P (r, 0) := by
  change overlap E J (L r, 1) = SSet.toTop.map (minusVertex E J)
    (P (r, unitInterval.symm 0))
  rw [unitInterval.symm_zero, h r, overlap_one]

/-- Literal half/quarter/quarter pasting, with full reference attachment at both seams. -/
def movingSquare : C(I × I, space E J) :=
  concatSecond (movingPlus E J P)
    (concatSecond (movingMiddle E J L) (movingMinus E J P)
      (moving_minus_seam E J P L h))
    (fun r ↦ (moving_plus_seam E J P L h r).trans
      (concatSecond_zero _ _ _ r).symm)

theorem movingSquare_lower (r t : I) :
    movingSquare E J P L h (r, lower t) =
      SSet.toTop.map (plusVertex E J) (P (r, t)) :=
  concatSecond_lower _ _ _ r t

theorem movingSquare_middle (r t : I) :
    movingSquare E J P L h (r, upper (lower t)) = overlap E J (L r, t) := by
  unfold movingSquare
  rw [concatSecond_upper, concatSecond_lower]
  rfl

theorem movingSquare_upper (r t : I) :
    movingSquare E J P L h (r, upper (upper t)) =
      SSet.toTop.map (minusVertex E J) (P (r, unitInterval.symm t)) := by
  unfold movingSquare
  rw [concatSecond_upper, concatSecond_upper]
  rfl

theorem movingSquare_left (r : I) :
    movingSquare E J P L h (r, 0) = SSet.toTop.map (plusVertex E J) (P (r, 0)) :=
  concatSecond_zero _ _ _ r

theorem movingSquare_right (r : I) :
    movingSquare E J P L h (r, 1) = SSet.toTop.map (minusVertex E J) (P (r, 0)) := by
  unfold movingSquare
  rw [concatSecond_one, concatSecond_one]
  change SSet.toTop.map (minusVertex E J) (P (r, unitInterval.symm 1)) = _
  rw [unitInterval.symm_one]

open LoopPrespectrum

/-- Evaluating this scalar square gives the chosen native square, including every original clock. -/
theorem movingSquare_native {B : LoopPrespectrum.{u}} (f : prespectrum V ⟶ B)
    {a₀ a₁ : prespectrum V ⟶ prespectrum W} {b₀ b₁ : B ⟶ prespectrum T}
    (H₀ : Homotopy (f ≫ b₀) (a₀ ≫ prespectrumMap J))
    (H₁ : Homotopy (f ≫ b₁) (a₁ ≫ prespectrumMap J))
    (C : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)
    (S : H₀.Square H₁ (Homotopy.precomp f M) (C.postcomp (prespectrumMap J)))
    (n : ℕ) (x : (prespectrum V).space n)
    (hP : ∀ r t : I, pointwisePrespectrumFamily (E ≫ J) n (P (r, t)) x =
      S.level n (r, (t, x)))
    (hL : ∀ r : I, pointwisePrespectrumFamily E n (L r) x = C.level n (r, x))
    (r s : I) :
    nativeEval E J n (movingSquare E J P L h (r, s)) x =
      (HomotopyPushout.identicalLegMovingSquare f (prespectrumMap J)
        H₀ H₁ C M S).level n (r, (s, x)) := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [movingSquare_lower, nativeEval_plus, HomotopyPushout.identicalMoving_lower]
    exact congrArg ((HomotopyPushout.inl (prespectrumMap J) (prespectrumMap J)).map n)
      (hP r t)
  · rcases cover t with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [movingSquare_middle, nativeEval_overlap, HomotopyPushout.identicalMoving_middle]
      exact congrArg (fun y ↦ HomotopyPushout.cylinder (prespectrumMap J)
        (prespectrumMap J) n (t, y)) (hL r)
    · rw [movingSquare_upper, nativeEval_minus, HomotopyPushout.identicalMoving_upper]
      exact congrArg ((HomotopyPushout.inr (prespectrumMap J) (prespectrumMap J)).map n)
        (hP r (unitInterval.symm t))

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
