/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTransitionNaturality
public import Quillen.Topology.Prespectrum.RelativeHomotopyNullWordEvaluation
public import Quillen.Topology.Prespectrum.RelativeLevelEvaluation

/-!
# Exact native postcomposition for the first left-route comparison

The original p rails are postcomposed by the original positive cone map of q. The
unchanged five-stage null word and two-sheet native conjugation retain every comparison
and path coordinate. Only zero endpoints and whole-level boundary types are transported.
There is no carrier map, evaluator, new geometric comparison, or comparison hypothesis.
-/
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

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftNativePostcomp

/-- The target zero endpoint is preserved by every based prespectrum map. -/
theorem zero_postcomp {E F G : LoopPrespectrum.{u}} (j : F ⟶ G) :
    zeroHom E F ≫ j = zeroHom E G := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact j.map_point n

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The positive Bass cone map induced by the coefficient arrow `q`. -/
abbrev coneMap := boundedFlatCoefficientBassPositiveConeMap P q

/-- The old positive-leg homotopy for `p`, postcomposed with the positive cone map of `q`. -/
abbrev oldPositive :=
  (CoefficientBassPositiveNullTrack.oldPositive P p).postcomp (coneMap P q)
/-- The positive coefficient-square homotopy for `p`, postcomposed with the cone map of `q`. -/
abbrev positiveMovement :=
  (CoefficientBassPositiveNullTrack.positiveMovement P p).postcomp (coneMap P q)
/-- The polynomial coefficient-square homotopy for `p`, postcomposed with the cone map of `q`. -/
abbrev polynomialMovement :=
  (CoefficientBassPositiveNullTrack.polynomialMovement P p).postcomp (coneMap P q)
/-- The Laurent coefficient-square homotopy for `p`, postcomposed with the cone map of `q`. -/
abbrev laurentMovement :=
  (CoefficientBassPositiveNullTrack.laurentMovement P p).postcomp (coneMap P q)
/-- The new positive-leg homotopy for `p`, postcomposed with the positive cone map of `q`. -/
abbrev newPositive :=
  (CoefficientBassPositiveNullTrack.newPositive P p).postcomp (coneMap P q)
/-- The old polynomial-leg cone contraction for `p`, postcomposed with the cone map of `q`. -/
abbrev oldCone :=
  (CoefficientBassPositiveNullTrack.oldCone P p).postcomp (coneMap P q)
/-- The new polynomial-leg cone contraction for `p`, postcomposed with the cone map of `q`. -/
abbrev newCone :=
  (CoefficientBassPositiveNullTrack.newCone P p).postcomp (coneMap P q)

/-- The original positive rectangle with its exact postcomposed boundary words. -/
def positivePasting :
    ((positiveMovement P p q).trans (polynomialMovement P p q)).RelHomotopy
      ((oldPositive P p q).symm.trans
        ((laurentMovement P p q).trans (newPositive P p q))) := by
  refine ((CoefficientBassPositiveNullTrack.positivePasting P p).postcomp
    (coneMap P q)).ofLevels _ _ ?_ ?_
  · intro n
    simp only [positiveMovement, polynomialMovement, Homotopy.postcomp_trans]
  · intro n
    simp only [oldPositive, laurentMovement, newPositive, Homotopy.postcomp_trans,
      Homotopy.postcomp_symm]

/-- The original cone collapse and pause cancellation with their exact new boundary types. -/
def conePasting : (oldCone P p q).RelHomotopy
    ((polynomialMovement P p q).trans (newCone P p q)) := by
  refine ((CoefficientBassPositiveNullTrack.conePasting P p).postcomp
    (coneMap P q)).ofLevels _ _ ?_ ?_
  · intro n
    rfl
  · intro n
    simp only [polynomialMovement, newCone, Homotopy.postcomp_trans]

/-- The original rectangle postcomposition retains both independent native times. -/
theorem positivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.positivePasting P p).MappedAt
      (coneMap P q) n x (positivePasting P p q) := by
  intro r s
  rfl

/-- The original cone comparison postcomposition retains its whole two-half recipe. -/
theorem conePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.conePasting P p).MappedAt
      (coneMap P q) n x (conePasting P p q) := by
  intro r s
  rfl

/-- The same straight-positive word used by native finite-carrier evaluation. -/
def straightPositivePasting := NativeNullWordEvaluation.Word.straightPositiveWord
  (oldPositive P p q) (positiveMovement P p q) (polynomialMovement P p q)
  (laurentMovement P p q) (newPositive P p q) (positivePasting P p q)

/-- The same five-stage pasted-null word used by native finite-carrier evaluation. -/
def pastedNullComparison := NativeNullWordEvaluation.Word.pastedPositiveNullWord
  (oldPositive P p q) (positiveMovement P p q) (polynomialMovement P p q)
  (laurentMovement P p q) (newPositive P p q) (oldCone P p q) (newCone P p q)
  (positivePasting P p q) (conePasting P p q)

/-- Every original associator and cancellation coordinate survives actual cone postcomposition. -/
theorem straightPositivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.straightPositivePasting P p).MappedAt
      (coneMap P q) n x (straightPositivePasting P p q) := by
  have hA : (CoefficientBassPositiveNullTrack.oldPositive P p).MappedAt
      (coneMap P q) n x (oldPositive P p q) := fun _ ↦ rfl
  have hB : (CoefficientBassPositiveNullTrack.positiveMovement P p).MappedAt
      (coneMap P q) n x (positiveMovement P p q) := fun _ ↦ rfl
  have hQ : (CoefficientBassPositiveNullTrack.polynomialMovement P p).MappedAt
      (coneMap P q) n x (polynomialMovement P p q) := fun _ ↦ rfl
  have hL : (CoefficientBassPositiveNullTrack.laurentMovement P p).MappedAt
      (coneMap P q) n x (laurentMovement P p q) := fun _ ↦ rfl
  have hF : (CoefficientBassPositiveNullTrack.newPositive P p).MappedAt
      (coneMap P q) n x (newPositive P p q) := fun _ ↦ rfl
  have hT := hL.trans hF
  exact (hA.transAssoc hB hQ).trans
    ((hA.refl.hcomp (positivePasting_mapped P p q n x)).trans
      ((hA.transAssoc hA.symm hT).symm.trans
        ((hA.reflTransSymm.symm.hcomp hT.refl).trans hT.reflTrans)))

/-- Postcomposition preserves the complete original five-stage pasted-null comparison. -/
theorem pastedNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.pastedNullComparison P p).MappedAt
      (coneMap P q) n x (pastedNullComparison P p q) := by
  have hA : (CoefficientBassPositiveNullTrack.oldPositive P p).MappedAt
      (coneMap P q) n x (oldPositive P p q) := fun _ ↦ rfl
  have hB : (CoefficientBassPositiveNullTrack.positiveMovement P p).MappedAt
      (coneMap P q) n x (positiveMovement P p q) := fun _ ↦ rfl
  have hQ : (CoefficientBassPositiveNullTrack.polynomialMovement P p).MappedAt
      (coneMap P q) n x (polynomialMovement P p q) := fun _ ↦ rfl
  have hE : (CoefficientBassPositiveNullTrack.oldCone P p).MappedAt
      (coneMap P q) n x (oldCone P p q) := fun _ ↦ rfl
  have hG : (CoefficientBassPositiveNullTrack.newCone P p).MappedAt
      (coneMap P q) n x (newCone P p q) := fun _ ↦ rfl
  have hL : (CoefficientBassPositiveNullTrack.laurentMovement P p).MappedAt
      (coneMap P q) n x (laurentMovement P p q) := fun _ ↦ rfl
  have hF : (CoefficientBassPositiveNullTrack.newPositive P p).MappedAt
      (coneMap P q) n x (newPositive P p q) := fun _ ↦ rfl
  exact (hA.transAssoc hB hE).symm.trans
    (((hA.trans hB).refl.hcomp (conePasting_mapped P p q n x)).trans
      (((hA.trans hB).transAssoc hQ hG).symm.trans
        (((straightPositivePasting_mapped P p q n x).hcomp hG.refl).trans
          (hL.transAssoc hF hG))))

/-- The original old null with only its zero endpoint transported through the actual cone map. -/
def originalOldNull :=
  ((CoefficientBassPositiveNullTrack.originalOldNull P p).postcomp (coneMap P q)).cast
    rfl (zero_postcomp (coneMap P q))

/-- The original new null with the same proof-only zero-endpoint transport. -/
def originalNewNull :=
  ((CoefficientBassPositiveNullTrack.originalNewNull P p).postcomp (coneMap P q)).cast
    rfl (zero_postcomp (coneMap P q))

/-- Every old-null level is the unchanged right-nested postcomposed positive/cone word. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull P p q).level n =
      ((oldPositive P p q).trans
        ((positiveMovement P p q).trans (oldCone P p q))).level n := by
  calc
    _ = ((CoefficientBassPositiveNullTrack.originalOldNull P p).postcomp
        (coneMap P q)).level n := rfl
    _ = (((CoefficientBassPositiveNullTrack.oldPositive P p).trans
        ((CoefficientBassPositiveNullTrack.positiveMovement P p).trans
          (CoefficientBassPositiveNullTrack.oldCone P p))).postcomp (coneMap P q)).level n :=
      Homotopy.postcomp_level_congr _ _ _ n
        (CoefficientBassPositiveNullTrack.originalOldNull_level P p n)
    _ = _ := by rw [Homotopy.postcomp_trans, Homotopy.postcomp_trans]

/-- Every new-null level is the unchanged positive leg followed by the mapped cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull P p q).level n =
      ((newPositive P p q).trans (newCone P p q)).level n := by
  calc
    _ = ((CoefficientBassPositiveNullTrack.originalNewNull P p).postcomp
        (coneMap P q)).level n := rfl
    _ = (((CoefficientBassPositiveNullTrack.newPositive P p).trans
        (CoefficientBassPositiveNullTrack.newCone P p)).postcomp (coneMap P q)).level n :=
      Homotopy.postcomp_level_congr _ _ _ n
        (CoefficientBassPositiveNullTrack.originalNewNull_level P p n)
    _ = _ := by rw [Homotopy.postcomp_trans]

/-- The original null endpoints are restored without changing any pasted-null value. -/
def originalNullComparison : (originalOldNull P p q).RelHomotopy
    ((laurentMovement P p q).trans (originalNewNull P p q)) := by
  refine (pastedNullComparison P p q).ofLevels _ _ (originalOldNull_level P p q) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level P p q n

/-- All whole-level endpoint transports preserve the exact original p null comparison. -/
theorem originalNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.originalNullComparison P p).MappedAt
      (coneMap P q) n x (originalNullComparison P p q) := by
  intro r s
  unfold originalNullComparison CoefficientBassPositiveNullTrack.originalNullComparison
  simp only [Homotopy.RelHomotopy.ofLevels_apply]
  exact pastedNullComparison_mapped P p q n x r s

/-- The old Laurent-unit loop for `p`, postcomposed with the positive cone map of `q`. -/
abbrev oldUnit :=
  (CoefficientBassPositiveTransitionTrack.oldUnit P p).postcomp (coneMap P q)
/-- The new Laurent-unit loop for `p`, postcomposed with the positive cone map of `q`. -/
abbrev newUnit :=
  (CoefficientBassPositiveTransitionTrack.newUnit P p).postcomp (coneMap P q)

/-- The original unit intertwining retains its full comparison and original boundary words. -/
def unitPasting : ((oldUnit P p q).trans (laurentMovement P p q)).RelHomotopy
    ((laurentMovement P p q).trans (newUnit P p q)) := by
  refine ((CoefficientBassPositiveTransitionTrack.unitPasting P p).postcomp
    (coneMap P q)).ofLevels _ _ ?_ ?_
  · intro n
    simp only [oldUnit, laurentMovement, Homotopy.postcomp_trans]
  · intro n
    simp only [newUnit, laurentMovement, Homotopy.postcomp_trans]

theorem unitPasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveTransitionTrack.unitPasting P p).MappedAt
      (coneMap P q) n x (unitPasting P p q) := by
  intro r s
  rfl

/-- The literal original conjugation recipe on the exact postcomposed native tracks. -/
def conjugateComparison := Homotopy.RelHomotopy.conjugateNaturality
  (laurentMovement P p q) (oldUnit P p q) (newUnit P p q)
  (originalOldNull P p q) (originalNewNull P p q)
  (unitPasting P p q) (originalNullComparison P p q)

/-- Actual cone postcomposition commutes with the whole original p conjugation word. -/
theorem conjugateComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveTransitionTrack.conjugateComparison P p).MappedAt
      (coneMap P q) n x (conjugateComparison P p q) := by
  unfold CoefficientBassPositiveTransitionTrack.conjugateComparison conjugateComparison
  apply Homotopy.RelHomotopy.conjugateNaturality_mapped
  · intro s
    rfl
  · intro s
    rfl
  · intro s
    rfl
  · intro s
    rfl
  · exact unitPasting_mapped P p q n x
  · exact originalNullComparison_mapped P p q n x

/-- Recovery targets the prescribed original J_p at its original comparison and loop times. -/
theorem conjugateComparison_transition (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (conjugateComparison P p q).level n (r, (s, x)) =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        (Path.toContinuousMap
          ((boundedFlatCoefficientBassPositiveTransitionHomotopy P p).level n (r, x)) s) := by
  rw [boundedFlatCoefficientBassPositiveTransitionHomotopy_apply]
  exact (conjugateComparison_mapped P p q n x r s).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftNativePostcomp
