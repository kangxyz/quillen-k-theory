/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeMovingSquare
public import Quillen.Topology.Prespectrum.SpanReassociationEvaluation

/-! The original moving-square stage followed by reversed five-piece reassociation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier Quillen.NativePathCells Quillen.ScalarRectangle
variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)
  {a b : |parameterSSet (E ≫ J)|} (e : |parameterSSet E|)
  (p : Path a b) (q : Path b (SSet.toTop.map (attachment E J) e))

/-- The original five leaves: two positive chart tracks, the overlap, and two reversed tracks. -/
def spanReassociation :=
  Path.Homotopy.spanReassociation
    (p.map (SSet.toTop.map (plusVertex E J)).hom.continuous)
    (q.map (SSet.toTop.map (plusVertex E J)).hom.continuous)
    (overlapPath E J e)
    (q.symm.map (SSet.toTop.map (minusVertex E J)).hom.continuous)
    (p.symm.map (SSet.toTop.map (minusVertex E J)).hom.continuous)

/-- The final word has precisely the two pasted polynomial tracks and the original overlap. -/
theorem spanReassociation_one (s : I) :
    spanReassociation E J e p q (1, s) =
      (((p.trans q).map (SSet.toTop.map (plusVertex E J)).hom.continuous).trans
        ((overlapPath E J e).trans
          ((p.trans q).symm.map (SSet.toTop.map (minusVertex E J)).hom.continuous))) s := by
  rw [(spanReassociation E J e p q).apply_one]
  simp only [Path.map_trans, Path.trans_symm]; rfl

variable (P : C(I × I, |parameterSSet (E ≫ J)|)) (L : C(I, |parameterSSet E|))
  (h : ∀ r : I, P (r, 1) = SSet.toTop.map (attachment E J) (L r))
  (he : L 1 = e) (hrow : ∀ s : I, P (1, s) = (p.trans q) s)

include he hrow in
/-- The whole time seam is a full scalar equality, before any native evaluation. -/
theorem spanComposition_join (s : I) :
    movingSquare E J P L h (1, s) = spanReassociation E J e p q (1, s) := by
  rw [spanReassociation_one]
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [movingSquare_lower, path_lower]
    exact congrArg (SSet.toTop.map (plusVertex E J)) (hrow t)
  · rcases cover t with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [movingSquare_middle, path_upper, path_lower, he]
      rfl
    · rw [movingSquare_upper, path_upper, path_upper]
      exact congrArg (SSet.toTop.map (minusVertex E J)) (hrow (unitInterval.symm t))

/-- The original A clock: vertex composition, then the reversed chosen reassociation. -/
def spanComposition : C(I × I, space E J) :=
  concatFirst (movingSquare E J P L h)
    (spanReassociation E J e p q).symm.toContinuousMap
    (by
      intro s
      change movingSquare E J P L h (1, s) =
        spanReassociation E J e p q (unitInterval.symm 0, s)
      rw [unitInterval.symm_zero]
      exact spanComposition_join E J e p q P L h he hrow s)

theorem spanComposition_lower (r s : I) :
    spanComposition E J e p q P L h he hrow (lower r, s) =
      movingSquare E J P L h (r, s) :=
  concatFirst_lower _ _ _ r s

theorem spanComposition_upper (r s : I) :
    spanComposition E J e p q P L h he hrow (upper r, s) =
      spanReassociation E J e p q (unitInterval.symm r, s) :=
  concatFirst_upper _ _ _ r s

/-- The positive chart boundary retains the original whole target-composition path. -/
def positiveChartPath : Path (SSet.toTop.map (plusVertex E J) (P (0, 0)))
    (SSet.toTop.map (plusVertex E J) (P (1, 0))) where
  toFun r := SSet.toTop.map (plusVertex E J) (P (r, 0))
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The inverse chart retains the same whole path in its distinct summand. -/
def negativeChartPath : Path (SSet.toTop.map (minusVertex E J) (P (0, 0)))
    (SSet.toTop.map (minusVertex E J) (P (1, 0))) where
  toFun r := SSet.toTop.map (minusVertex E J) (P (r, 0))
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The entire positive edge has exactly the final constant half of the original A. -/
theorem spanComposition_left (r : I) :
    spanComposition E J e p q P L h he hrow (r, 0) =
      ((positiveChartPath E J P).trans (Path.refl _)) r := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [spanComposition_lower, movingSquare_left, path_lower]
    rfl
  · rw [spanComposition_upper, path_upper]
    have hs := (spanReassociation E J e p q).source (unitInterval.symm t)
    have ha : P (1, 0) = a := (hrow 0).trans (p.trans q).source
    exact hs.trans (congrArg (SSet.toTop.map (plusVertex E J)) ha.symm)

/-- The distinct inverse edge has the same unchanged terminal half pause. -/
theorem spanComposition_right (r : I) :
    spanComposition E J e p q P L h he hrow (r, 1) =
      ((negativeChartPath E J P).trans (Path.refl _)) r := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [spanComposition_lower, movingSquare_right, path_lower]
    rfl
  · rw [spanComposition_upper, path_upper]
    have hs := (spanReassociation E J e p q).target (unitInterval.symm t)
    have ha : P (1, 0) = a := (hrow 0).trans (p.trans q).source
    exact hs.trans (congrArg (SSet.toTop.map (minusVertex E J)) ha.symm)

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
