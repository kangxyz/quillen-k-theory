/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-! The original positive-chart source null on arbitrary native coefficient fibers
compares through the actual coefficient cone map. The full moving null uses the
existing positive geometric pasting and independent source-leg/cone interchange. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNullTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The original positive-leg track after Laurent coefficient change and cone inclusion. -/
def oldPositive :=
  ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The actual positive coefficient square on the original polynomial projection. -/
def positiveMovement :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The original polynomial coefficient track followed by the target positive Laurent leg. -/
def polynomialMovement :=
  ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The original common Laurent coefficient square after target cone inclusion. -/
def laurentMovement :=
  (boundedFlatCoefficientLaurentSquareHomotopy P u).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The target positive-leg comparison preceded by the original base coefficient map. -/
def newPositive :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatCoefficientLaurentPlusHomotopy P b)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The previously proved geometric positive-chart pasting retains its full cone-image track. -/
def positivePasting :
    ((positiveMovement P u).trans (polynomialMovement P u)).RelHomotopy
      ((oldPositive P u).symm.trans ((laurentMovement P u).trans (newPositive P u))) := by
  simpa only [boundedFlatCoefficientPlusLeftTrack, boundedFlatCoefficientPlusRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm, positiveMovement, polynomialMovement,
    oldPositive, laurentMovement, newPositive] using
    (boundedFlatCoefficientPlusPasting P u).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

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
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatCoefficientBassSourceLeg P a ≫
    boundedFlatCoefficientPolynomialSpanMap P u)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The new source-leg image traverses the same original target cone cylinder. -/
def newCone : Homotopy
    (((boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus P b)) ≫
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
    boundedFlatCoefficientBassSourceLeg P b)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b))).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The original source-leg cone square supplies its actual polynomial-movement pasting. -/
def conePasting :
    (oldCone P u).RelHomotopy ((polynomialMovement P u).trans (newCone P u)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
    (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))
    (mappingCone (boundedFlatCoefficientBassSquareComparison P b)))
  have J : (oldCone P u).RelHomotopy
      (((polynomialMovement P u).trans (newCone P u)).trans Z) := by
    refine (boundedFlatCoefficientBassSourceLegConeBoundary P u).ofLevels _ _ ?_ ?_
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
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)) (zeroHom _ _) :=
  ((boundedFlatCoefficientBassLaurentNullHomotopy P a).postcomp
    (boundedFlatCoefficientBassConeMap P u)).cast (by
    apply Hom.ext
    funext n
    ext x
    rfl) (by
      apply Hom.ext
      funext n
      ext x
      exact (boundedFlatCoefficientBassConeMap P u).map_point n)

/-- The original target-fiber Laurent nullhomotopy preceded by actual base coefficient change. -/
def originalNewNull : Homotopy
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (laurentProjection P b)) ≫
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatCoefficientBassLaurentNullHomotopy P b)).cast (Category.assoc _ _ _).symm rfl

/-- Every original target-null coordinate is its unchanged positive leg and cone cylinder. -/
lemma originalNewNull_level (n : ℕ) :
    (originalNewNull P u).level n = ((newPositive P u).trans (newCone P u)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    ((boundedFlatCoefficientLaurentPlusHomotopy P b).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)))).trans
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (Homotopy.precomp (boundedFlatCoefficientBassSourceLeg P b)
          (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Each mapped old-null coordinate retains the positive leg and actual cone-square map. -/
lemma originalOldNull_level (n : ℕ) :
    (originalOldNull P u).level n =
      ((oldPositive P u).trans ((positiveMovement P u).trans (oldCone P u))).level n := by
  unfold originalOldNull
  rw [Homotopy.cast_level]
  change ((((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans
      (Homotopy.precomp (boundedFlatCoefficientBassSourceLeg P a)
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)))).postcomp
          (boundedFlatCoefficientBassConeMap P u)).level n = _
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

end Quillen.PerfectComplexes.CoefficientBassNullTrack
