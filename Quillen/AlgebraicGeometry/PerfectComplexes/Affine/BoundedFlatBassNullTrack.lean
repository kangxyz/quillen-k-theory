/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSourceLeg
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! Original geometric tracks in the coefficient comparison of the Bass Laurent nullhomotopy. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent Quillen.PolynomialBaseChange
universe u
namespace Quillen.PerfectComplexes.BassNullTrack
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original positive-leg track after Laurent coefficient change and cone inclusion. -/
def oldPositive :=
  ((boundedFlatLaurentPlusHomotopy R).postcomp
    (boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f)))).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The actual positive coefficient square on the original polynomial projection. -/
def positiveMovement :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPlusSquareHomotopy f)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
        (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The original polynomial coefficient track followed by the target positive Laurent leg. -/
def polynomialMovement :=
  ((boundedFlatPolynomialSquareHomotopy f).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus S))).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The original common Laurent coefficient square after target cone inclusion. -/
def laurentMovement :=
  (boundedFlatLaurentCoefficientSquareHomotopy f).postcomp
    (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The target positive-leg comparison preceded by the original base coefficient map. -/
def newPositive :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
    (boundedFlatLaurentPlusHomotopy S)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The previously proved geometric positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement f).trans (polynomialMovement f)).RelHomotopy
      ((oldPositive f).symm.trans ((laurentMovement f).trans (newPositive f))) := by
  simpa only [boundedFlatPlusCoefficientLeftTrack, boundedFlatPlusCoefficientRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement, polynomialMovement,
    oldPositive, laurentMovement, newPositive] using
    (boundedFlatPlusCoefficientPasting f).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- Cancel the actual positive-leg inverse to recover the genuine three-track geometric route. -/
def straightPositivePasting :
    (((oldPositive f).trans (positiveMovement f)).trans
      (polynomialMovement f)).RelHomotopy
        ((laurentMovement f).trans (newPositive f)) := by
  let A := oldPositive f
  let B := positiveMovement f
  let P := polynomialMovement f
  let T := (laurentMovement f).trans (newPositive f)
  exact (Homotopy.RelHomotopy.transAssoc A B P).trans
    (((Homotopy.RelHomotopy.refl A).hcomp (positivePasting f)).trans
      ((Homotopy.RelHomotopy.transAssoc A A.symm T).symm.trans
        (((Homotopy.RelHomotopy.reflTransSymm A).symm.hcomp
          (Homotopy.RelHomotopy.refl T)).trans (Homotopy.RelHomotopy.reflTrans T))))

/-- The old source-leg image traverses the original target cone cylinder. -/
def oldCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (polynomialMap f))) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus S)) ≫
      mappingConeInclusion (boundedFlatBassSquareComparison S)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatBassSourceLeg R ≫ boundedFlatPolynomialSpanMap f)
    (mappingConeHomotopy (boundedFlatBassSquareComparison S))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The new source-leg image traverses the same original target cone cylinder. -/
def newCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (Spec.map f) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection S)) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus S)) ≫
      mappingConeInclusion (boundedFlatBassSquareComparison S)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f) ≫ boundedFlatBassSourceLeg S)
    (mappingConeHomotopy (boundedFlatBassSquareComparison S))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The original source-leg cone square supplies its actual polynomial-movement pasting. -/
def conePasting :
    (oldCone f).RelHomotopy ((polynomialMovement f).trans (newCone f)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
    (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))
    (mappingCone (boundedFlatBassSquareComparison S)))
  have J : (oldCone f).RelHomotopy
      (((polynomialMovement f).trans (newCone f)).trans Z) := by
    refine (boundedFlatBassSourceLegConeBoundary f).ofLevels _ _ ?_ ?_
    · intro n
      rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext
          rintro ⟨s, x⟩
          rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- The original positive geometry and actual cone square paste to the target null route. -/
def pastedNullComparison :
    ((oldPositive f).trans ((positiveMovement f).trans (oldCone f))).RelHomotopy
      ((laurentMovement f).trans ((newPositive f).trans (newCone f))) := by
  let A := oldPositive f
  let B := positiveMovement f
  let P := polynomialMovement f
  let E := oldCone f
  let G := newCone f
  let L := laurentMovement f
  let F := newPositive f
  exact (Homotopy.RelHomotopy.transAssoc A B E).symm.trans
    (((Homotopy.RelHomotopy.refl (A.trans B)).hcomp (conePasting f)).trans
      ((Homotopy.RelHomotopy.transAssoc (A.trans B) P G).symm.trans
        (((straightPositivePasting f).hcomp (Homotopy.RelHomotopy.refl G)).trans
          (Homotopy.RelHomotopy.transAssoc L F G))))

/-- The original old-ring Laurent nullhomotopy followed by the actual coefficient cone map. -/
def originalOldNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (laurentProjection R) ≫
      boundedFlatPerfectPrespectrumMap (Spec.map (laurentMap f))) ≫
      mappingConeInclusion (boundedFlatBassSquareComparison S)) (zeroHom _ _) :=
  ((boundedFlatBassLaurentNullHomotopy R).postcomp (boundedFlatBassConeMap f)).cast (by
    apply Hom.ext
    funext n
    ext x
    rfl) (by
      apply Hom.ext
      funext n
      ext x
      exact (boundedFlatBassConeMap f).map_point n)

/-- The original target Laurent nullhomotopy preceded by actual base coefficient change. -/
def originalNewNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (Spec.map f) ≫
      boundedFlatPerfectPrespectrumMap (laurentProjection S)) ≫
      mappingConeInclusion (boundedFlatBassSquareComparison S)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
    (boundedFlatBassLaurentNullHomotopy S)).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull f).level n = ((newPositive f).trans (newCone f)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
    ((boundedFlatLaurentPlusHomotopy S).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S)))).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
        (Homotopy.precomp (boundedFlatBassSourceLeg S)
          (mappingConeHomotopy (boundedFlatBassSquareComparison S))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull f).level n =
      ((oldPositive f).trans ((positiveMovement f).trans (oldCone f))).level n := by
  unfold originalOldNull
  rw [Homotopy.cast_level]
  change ((((boundedFlatLaurentPlusHomotopy R).postcomp
    (mappingConeInclusion (boundedFlatBassSquareComparison R))).trans
      (Homotopy.precomp (boundedFlatBassSourceLeg R)
        (mappingConeHomotopy (boundedFlatBassSquareComparison R)))).postcomp
          (boundedFlatBassConeMap f)).level n = _
  rw [Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    rfl

/-- The two unchanged Laurent nullhomotopies compare along the actual Laurent coefficient track. -/
def originalNullComparison :
    (originalOldNull f).RelHomotopy ((laurentMovement f).trans (originalNewNull f)) := by
  refine (pastedNullComparison f).ofLevels _ _ (originalOldNull_level f) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level f n

end Quillen.PerfectComplexes.BassNullTrack
