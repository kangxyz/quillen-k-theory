/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNullTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Quillen.Topology.Prespectrum.RelativeHomotopyPostcompReparam

/-! The unchanged original positive-null pasting is performed in the actual positive cones.
The same geometric pasting, polynomial/cone interchange, associators and cancellations retain
every original comparison and null coordinate. Exact image comparison with the chosen full-cone
recipe is a separate theorem; no mixed higher filler is supplied here. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveNullTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The original positive-leg track after Laurent coefficient change and cone inclusion. -/
def oldPositive :=
  ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The actual positive coefficient square on the original polynomial projection. -/
def positiveMovement :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
        (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The original polynomial coefficient track followed by the target positive Laurent leg. -/
def polynomialMovement :=
  ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The original common Laurent coefficient square after target cone inclusion. -/
def laurentMovement :=
  (boundedFlatCoefficientLaurentSquareHomotopy P u).postcomp
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The target positive-leg comparison preceded by the original base coefficient map. -/
def newPositive :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatCoefficientLaurentPlusHomotopy P b)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The previously proved geometric positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement P u).trans (polynomialMovement P u)).RelHomotopy
      ((oldPositive P u).symm.trans ((laurentMovement P u).trans (newPositive P u))) := by
  simpa only [boundedFlatCoefficientPlusLeftTrack, boundedFlatCoefficientPlusRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement, polynomialMovement,
    oldPositive, laurentMovement, newPositive] using
    (boundedFlatCoefficientPlusPasting P u).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- Cancel the actual positive-leg inverse to recover the genuine three-track geometric route. -/
def straightPositivePasting :
    (((oldPositive P u).trans (positiveMovement P u)).trans
      (polynomialMovement P u)).RelHomotopy
        ((laurentMovement P u).trans (newPositive P u)) := by
  let A := oldPositive P u
  let B := positiveMovement P u
  let Q := polynomialMovement P u
  let T := (laurentMovement P u).trans (newPositive P u)
  exact (Homotopy.RelHomotopy.transAssoc A B Q).trans
    (((Homotopy.RelHomotopy.refl A).hcomp (positivePasting P u)).trans
      ((Homotopy.RelHomotopy.transAssoc A A.symm T).symm.trans
        (((Homotopy.RelHomotopy.reflTransSymm A).symm.hcomp
          (Homotopy.RelHomotopy.refl T)).trans (Homotopy.RelHomotopy.reflTrans T))))

/-- The old source-leg image traverses the original target cone cylinder. -/
def oldCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u))) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus P b)) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
    boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The new source-leg image traverses the same original target cone cylinder. -/
def newCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus P b)) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
    boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
    (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The original source-leg cone square supplies its actual polynomial-movement pasting. -/
def conePasting :
    (oldCone P u).RelHomotopy ((polynomialMovement P u).trans (newCone P u)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
    (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))
    (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))))
  have J : (oldCone P u).RelHomotopy
      (((polynomialMovement P u).trans (newCone P u)).trans Z) := by
    refine ((Homotopy.Square.interchange (boundedFlatCoefficientPolynomialSquareHomotopy P u)
      (mappingConeHomotopy
        (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))).toBoundary).ofLevels _ _ ?_ ?_
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
    ((oldPositive P u).trans ((positiveMovement P u).trans (oldCone P u))).RelHomotopy
      ((laurentMovement P u).trans ((newPositive P u).trans (newCone P u))) := by
  let A := oldPositive P u
  let B := positiveMovement P u
  let Q := polynomialMovement P u
  let E := oldCone P u
  let G := newCone P u
  let L := laurentMovement P u
  let F := newPositive P u
  exact (Homotopy.RelHomotopy.transAssoc A B E).symm.trans
    (((Homotopy.RelHomotopy.refl (A.trans B)).hcomp (conePasting P u)).trans
      ((Homotopy.RelHomotopy.transAssoc (A.trans B) Q G).symm.trans
        (((straightPositivePasting P u).hcomp (Homotopy.RelHomotopy.refl G)).trans
          (Homotopy.RelHomotopy.transAssoc L F G))))

/-- The original old-fiber Laurent nullhomotopy followed by the actual coefficient cone map. -/
def originalOldNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (laurentProjection P a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u))) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))) (zeroHom _ _) :=
  ((boundedFlatCoefficientBassPositiveConeNull P a).postcomp
    (boundedFlatCoefficientBassPositiveConeMap P u)).cast (by
    apply Hom.ext
    funext n
    ext x
    rfl) (by
      apply Hom.ext
      funext n
      ext x
      exact (boundedFlatCoefficientBassPositiveConeMap P u).map_point n)

/-- The original target-fiber Laurent nullhomotopy preceded by actual base coefficient change. -/
def originalNewNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (laurentProjection P b)) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatCoefficientBassPositiveConeNull P b)).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull P u).level n = ((newPositive P u).trans (newCone P u)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    ((boundedFlatCoefficientLaurentPlusHomotopy P b).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))))).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
          (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull P u).level n =
      ((oldPositive P u).trans ((positiveMovement P u).trans (oldCone P u))).level n := by
  unfold originalOldNull
  rw [Homotopy.cast_level]
  change ((((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P a))))).postcomp
          (boundedFlatCoefficientBassPositiveConeMap P u)).level n = _
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
    (originalOldNull P u).RelHomotopy ((laurentMovement P u).trans (originalNewNull P u)) := by
  refine (pastedNullComparison P u).ofLevels _ _ (originalOldNull_level P u) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level P u n


/-- The strict positive inclusion preserves the whole original old positive track. -/
theorem oldPositive_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (oldPositive P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.oldPositive P u) := by
  intro s
  rfl

/-- The strict positive inclusion preserves the actual moving positive chart. -/
theorem positiveMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (positiveMovement P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.positiveMovement P u) := by
  intro s
  rfl

/-- The original polynomial coefficient movement is unchanged at every time. -/
theorem polynomialMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (polynomialMovement P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.polynomialMovement P u) := by
  intro s
  rfl

/-- The original common Laurent movement is unchanged at every time. -/
theorem laurentMovement_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (laurentMovement P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.laurentMovement P u) := by
  intro s
  rfl

/-- The strict positive inclusion preserves the whole original new positive track. -/
theorem newPositive_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (newPositive P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.newPositive P u) := by
  intro s
  rfl

/-- The old cone cylinder keeps exactly the same original cylinder coordinate. -/
theorem oldCone_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (oldCone P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.oldCone P u) := by
  intro s
  rfl

/-- The new cone cylinder keeps exactly the same original cylinder coordinate. -/
theorem newCone_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (newCone P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.newCone P u) := by
  intro s
  rfl

/-- The full supplied positive geometric pasting has its exact original cone image. -/
theorem positivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (positivePasting P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.positivePasting P u) := by
  unfold positivePasting CoefficientBassNullTrack.positivePasting
  apply Homotopy.RelHomotopy.MappedAt.transport
  all_goals try simp only [boundedFlatCoefficientPlusLeftTrack,
    boundedFlatCoefficientPlusRightTrack, Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    positiveMovement, polynomialMovement, oldPositive, laurentMovement, newPositive,
    CoefficientBassNullTrack.positiveMovement, CoefficientBassNullTrack.polynomialMovement,
    CoefficientBassNullTrack.oldPositive, CoefficientBassNullTrack.laurentMovement,
    CoefficientBassNullTrack.newPositive]
  intro r s
  rfl

/-- Every original associator and cancellation coordinate is retained in the positive pasting. -/
theorem straightPositivePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (straightPositivePasting P u).MappedAt
      (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.straightPositivePasting P u) := by
  have hA := oldPositive_mapped P u n x
  have hB := positiveMovement_mapped P u n x
  have hQ := polynomialMovement_mapped P u n x
  have hT := (laurentMovement_mapped P u n x).trans (newPositive_mapped P u n x)
  exact (hA.transAssoc hB hQ).trans
    ((hA.refl.hcomp (positivePasting_mapped P u n x)).trans
      ((hA.transAssoc hA.symm hT).symm.trans
        ((hA.reflTransSymm.symm.hcomp hT.refl).trans hT.reflTrans)))

/-- The actual polynomial/cone interchange and its full boundary collapse map to the old one. -/
theorem conePasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (conePasting P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.conePasting P u) := by
  unfold conePasting CoefficientBassNullTrack.conePasting
  apply Homotopy.RelHomotopy.MappedAt.trans
  · intro r s
    rfl
  · exact ((polynomialMovement_mapped P u n x).trans (newCone_mapped P u n x)).transRefl

/-- The complete original null recipe preserves all its actual relative subdivisions. -/
theorem pastedNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (pastedNullComparison P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.pastedNullComparison P u) := by
  have hA := oldPositive_mapped P u n x
  have hB := positiveMovement_mapped P u n x
  have hQ := polynomialMovement_mapped P u n x
  have hE := oldCone_mapped P u n x
  have hG := newCone_mapped P u n x
  have hL := laurentMovement_mapped P u n x
  have hF := newPositive_mapped P u n x
  exact (hA.transAssoc hB hE).symm.trans
    (((hA.trans hB).refl.hcomp (conePasting_mapped P u n x)).trans
      (((hA.trans hB).transAssoc hQ hG).symm.trans
        (((straightPositivePasting_mapped P u n x).hcomp hG.refl).trans
          (hL.transAssoc hF hG))))

/-- The chosen original null comparison is literally the positive one after strict inclusion. -/
theorem originalNullComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (originalNullComparison P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.originalNullComparison P u) :=
  pastedNullComparison_mapped P u n x

end Quillen.PerfectComplexes.CoefficientBassPositiveNullTrack
