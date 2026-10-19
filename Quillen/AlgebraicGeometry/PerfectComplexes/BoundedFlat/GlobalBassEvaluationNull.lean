/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationSourceLeg
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Original Bass nullhomotopies under section evaluation

The proved positive-chart pasting and actual source-leg cone square compare the unchanged
strict and raw Laurent nullhomotopies, preserving every original cylinder parameter.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluationNull
open GlobalBassEvaluation GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- Original positive chart evaluation, with only its strict starting equality transported. -/
def positiveMovement :=
  (chartFirstTrack X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The original polynomial evaluation track followed by the raw positive Laurent leg. -/
def polynomialMovement :=
  (chartSecondTrack X (plus.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The unchanged Laurent coefficient evaluation track followed by raw cone inclusion. -/
def laurentMovement :=
  (evaluationComparison (GlobalRawBass.laurentProjection.app X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))

/-- Original raw positive composition, preceded by the original base evaluation. -/
def newPositive :=
  ((Homotopy.precomp (evaluation X)
    (GlobalRawBass.plusHomotopy X)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The actual positive-chart geometric equation retains its whole cone image. -/
def positivePasting :
    ((positiveMovement X).trans (polynomialMovement X)).RelHomotopy
      ((laurentMovement X).trans (newPositive X)) := by
  refine ((chartPasting X (plus.app X) (GlobalRawBass.plus_projection X)).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))).ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl
  · intro n
    rw [chartOuterTrack, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · rfl
    · rfl

/-- The evaluated strict source leg traverses the original raw cone cylinder. -/
def oldCone : Homotopy
    (((sectionMap (projection.app X) ≫
      evaluation (polynomial.obj X)) ≫
        boundedFlatPerfectPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (StrictSquare.sourceLeg (sectionSquare X) ≫
    spanEvaluation X)
    (mappingConeHomotopy (GlobalRawBass.comparison X))).cast
      (by apply Hom.ext; funext n; ext x; rfl) rfl

/-- The base evaluation followed by the raw source leg traverses that same cone cylinder. -/
def newCone : Homotopy
    (((evaluation X ≫
      boundedFlatPerfectPrespectrumMap (projection.app X)) ≫
        boundedFlatPerfectPrespectrumMap (plus.app X)) ≫
          mappingConeInclusion (GlobalRawBass.comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (evaluation X ≫
    GlobalRawBass.sourceLeg X) (mappingConeHomotopy (GlobalRawBass.comparison X))).cast
      (by apply Hom.ext; funext n; ext x; rfl) rfl

/-- The actual source-leg cone square supplies the whole polynomial-movement boundary. -/
def conePasting :
    (oldCone X).RelHomotopy ((polynomialMovement X).trans (newCone X)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl
    (zeroHom (GlobalSchemeLaurentTrack.diagram.obj (Opposite.op X))
      (mappingCone (GlobalRawBass.comparison X)))
  have J : (oldCone X).RelHomotopy
      (((polynomialMovement X).trans (newCone X)).trans Z) := by
    refine (sourceLegConeBoundary X).ofLevels _ _ ?_ ?_
    · intro n; rfl
    · intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr
        · apply ContinuousMap.ext; rintro ⟨s, x⟩; rfl
        · rfl
      · rfl
  exact J.trans (Homotopy.RelHomotopy.transRefl _)

/-- Original geometric pasting combines with the cone movement without changing any track. -/
def pastedNullComparison :
    ((positiveMovement X).trans (oldCone X)).RelHomotopy
      ((laurentMovement X).trans ((newPositive X).trans (newCone X))) :=
  ((Homotopy.RelHomotopy.refl (positiveMovement X)).hcomp (conePasting X)).trans
    ((Homotopy.RelHomotopy.transAssoc _ _ _).symm.trans
      (((positivePasting X).hcomp (Homotopy.RelHomotopy.refl (newCone X))).trans
        (Homotopy.RelHomotopy.transAssoc _ _ _)))

/-- The unchanged strict nullhomotopy followed by the actual proved cone evaluation. -/
def originalOldNull : Homotopy
    ((sectionMap (GlobalRawBass.laurentProjection.app X) ≫
      evaluation (laurent.obj X)) ≫
        mappingConeInclusion (GlobalRawBass.comparison X)) (zeroHom _ _) :=
  ((strictSourceNull X).postcomp
    (coneEvaluation X)).cast
      (by rw [Category.assoc, coneEvaluation_inclusion,
        ← Category.assoc])
      (by apply Hom.ext; funext n; ext x
          exact (coneEvaluation X).map_point n)

/-- The unchanged raw nullhomotopy preceded by the actual original base evaluation. -/
def originalNewNull : Homotopy
    ((evaluation X ≫
      boundedFlatPerfectPrespectrumMap (GlobalRawBass.laurentProjection.app X)) ≫
        mappingConeInclusion (GlobalRawBass.comparison X)) (zeroHom _ _) :=
  (Homotopy.precomp (evaluation X)
    (GlobalRawBass.sourceNull X)).cast (Category.assoc _ _ _).symm rfl

/-- Every original raw-null coordinate retains its positive track and actual cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull X).level n = ((newPositive X).trans (newCone X)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (evaluation X)
    ((GlobalRawBass.plusHomotopy X).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X)))).trans
      (Homotopy.precomp (evaluation X)
        (Homotopy.precomp (GlobalRawBass.sourceLeg X)
          (mappingConeHomotopy (GlobalRawBass.comparison X))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- The original strict-null image retains the full comparison track and raw cone coordinate. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull X).level n = ((positiveMovement X).trans (oldCone X)).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  rfl

/-- The unchanged original Laurent nullhomotopies compare along actual Laurent evaluation. -/
def originalNullComparison :
    (originalOldNull X).RelHomotopy ((laurentMovement X).trans (originalNewNull X)) := by
  refine (pastedNullComparison X).ofLevels _ _ (originalOldNull_level X) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level X n

end Quillen.PerfectComplexes.GlobalBassEvaluationNull
