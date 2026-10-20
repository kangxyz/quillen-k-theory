/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareSplitEvaluation

/-!
# The original strict source-null under split-square evaluation

The source null is the original undelayed strict cone cylinder. Its image under the actual
cone evaluation is the positive chart movement followed by the target cone cylinder. The
proved chart pasting and source-leg interchange compare this whole image with the prescribed
split target null along the common diagonal movement. No localization null is involved.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.StrictSquare.SplitEvaluation.Null
variable {S : Arrow (Arrow LoopPrespectrum.{u})} {R : SplitSquare.{u}}
  (i : SplitEvaluation S R)

/-- The original positive chart movement followed by target cone inclusion. -/
def positiveMovement := (positiveTrack i).postcomp (mappingConeInclusion R.comparison)

/-- The original positive projection movement followed by the target positive chart. -/
def polynomialMovement := (i.Qp.postcomp R.p).postcomp (mappingConeInclusion R.comparison)

/-- The common original diagonal movement followed by target cone inclusion. -/
def diagonalMovement := i.T.postcomp (mappingConeInclusion R.comparison)

/-- The actual target positive split track preceded by source evaluation. -/
def newPositive :=
  ((Homotopy.precomp i.a R.Dp).cast rfl (Category.assoc _ _ _).symm).postcomp
    (mappingConeInclusion R.comparison)

/-- The proved positive chart pasting retains its entire cone image. -/
def positivePasting :
    ((positiveMovement i).trans (polynomialMovement i)).RelHomotopy
      ((diagonalMovement i).trans (newPositive i)) := by
  simpa only [Homotopy.postcomp_trans, positiveMovement, polynomialMovement,
    diagonalMovement, newPositive, positiveTrack] using
    i.Jp.postcomp (mappingConeInclusion R.comparison)

/-- The evaluated original strict source leg traverses the target cone cylinder. -/
def oldCone : Homotopy
    (((S.left.hom ≫ i.bp) ≫ R.p) ≫ mappingConeInclusion R.comparison) (zeroHom _ _) :=
  (Homotopy.precomp (StrictSquare.sourceLeg S ≫ spanMap i)
    (mappingConeHomotopy R.comparison)).cast (by
      apply Hom.ext
      funext n
      ext x
      rfl) rfl

/-- The evaluated base followed by the original split source leg traverses that cylinder. -/
def newCone : Homotopy
    (((i.a ≫ R.pi) ≫ R.p) ≫ mappingConeInclusion R.comparison) (zeroHom _ _) :=
  (Homotopy.precomp (i.a ≫ R.sourceLeg) (mappingConeHomotopy R.comparison)).cast (by
    apply Hom.ext
    funext n
    ext x
    rfl) rfl

/-- The original source-leg interchange supplies its whole projection-movement boundary. -/
def conePasting :
    (oldCone i).RelHomotopy ((polynomialMovement i).trans (newCone i)) := by
  let Z := Homotopy.refl (zeroHom S.left.left (mappingCone R.comparison))
  have J : (oldCone i).RelHomotopy (((polynomialMovement i).trans (newCone i)).trans Z) := by
    refine (sourceLegConeBoundary i).ofLevels _ _ ?_ ?_
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

/-- Actual positive-chart pasting and cone movement preserve all prescribed null segments. -/
def pastedNullComparison :
    ((positiveMovement i).trans (oldCone i)).RelHomotopy
      ((diagonalMovement i).trans ((newPositive i).trans (newCone i))) :=
  ((Homotopy.RelHomotopy.refl (positiveMovement i)).hcomp (conePasting i)).trans
    ((Homotopy.RelHomotopy.transAssoc _ _ _).symm.trans
      (((positivePasting i).hcomp (Homotopy.RelHomotopy.refl (newCone i))).trans
        (Homotopy.RelHomotopy.transAssoc _ _ _)))

/-- The unchanged undelayed strict null followed by the actual evaluation cone map. -/
def originalOldNull : Homotopy
    (((S.left.hom ≫ S.hom.right) ≫ i.c) ≫ mappingConeInclusion R.comparison)
      (zeroHom _ _) :=
  ((StrictSquare.sourceNullHomotopy S).postcomp (coneMap i)).cast
    (by rw [Category.assoc, coneMap_inclusion, ← Category.assoc])
    (by
      apply Hom.ext
      funext n
      ext x
      exact (coneMap i).map_point n)

/-- The unchanged split target null preceded by source-corner evaluation. -/
def originalNewNull : Homotopy
    ((i.a ≫ R.l) ≫ mappingConeInclusion R.comparison) (zeroHom _ _) :=
  (Homotopy.precomp i.a R.sourceNull).cast (Category.assoc _ _ _).symm rfl

/-- Every target-null point retains its positive split track and original cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull i).level n = ((newPositive i).trans (newCone i)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp i.a (R.Dp.postcomp (mappingConeInclusion R.comparison))).trans
    (Homotopy.precomp i.a
      (Homotopy.precomp R.sourceLeg (mappingConeHomotopy R.comparison)))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- Evaluation of the original full strict cylinder retains the actual positive moving edge. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull i).level n = ((positiveMovement i).trans (oldCone i)).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  rfl

/-- The two specified whole nullhomotopies compare along actual diagonal evaluation. -/
def originalNullComparison :
    (originalOldNull i).RelHomotopy ((diagonalMovement i).trans (originalNewNull i)) := by
  refine (pastedNullComparison i).ofLevels _ _ (originalOldNull_level i) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level i n

end Quillen.LoopPrespectrum.StrictSquare.SplitEvaluation.Null
