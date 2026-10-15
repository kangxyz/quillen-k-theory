/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Aglib.Algebra.Polynomial.Laurent.Square
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluationSourceLeg
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Original Bass nullhomotopies under section evaluation

The proved positive-chart pasting and actual source-leg cone square compare the unchanged
strict and raw Laurent nullhomotopies, preserving every original cylinder parameter.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.SectionBassEvaluationNull
variable (R : CommRingCat.{u})

/-- Original positive chart evaluation, with only its strict starting equality transported. -/
def positiveMovement :=
  (boundedFlatAffineSectionChartFirstTrack R (CommRingCat.ofHom Polynomial.toLaurent)
    (coefficient_toLaurent R)).postcomp (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- The original polynomial evaluation track followed by the raw positive Laurent leg. -/
def polynomialMovement :=
  (boundedFlatAffineSectionChartSecondTrack R (CommRingCat.ofHom Polynomial.toLaurent)).postcomp
    (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- The unchanged Laurent coefficient evaluation track followed by raw cone inclusion. -/
def laurentMovement :=
  (boundedFlatAffineSectionEvaluationCoefficientHomotopy (laurentCoefficient R)).postcomp
    (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- Original raw positive composition, preceded by the original base evaluation. -/
def newPositive :=
  ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatLaurentPlusHomotopy R)).cast rfl (Category.assoc _ _ _).symm).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))

/-- The actual positive-chart geometric equation retains its whole cone image. -/
def positivePasting :
    ((positiveMovement R).trans (polynomialMovement R)).RelHomotopy
      ((laurentMovement R).trans (newPositive R)) := by
  refine ((boundedFlatAffineSectionChartFirstPasting R
    (CommRingCat.ofHom Polynomial.toLaurent) (coefficient_toLaurent R)).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))).ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl
  · intro n
    rw [boundedFlatAffineSectionChartOuterTrack, Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr
    · rfl
    · rfl

/-- The evaluated strict source leg traverses the original raw cone cylinder. -/
def oldCone : Homotopy
    (((boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R)) ≫
          mappingConeInclusion (boundedFlatBassSquareComparison R)) (zeroHom _ _) :=
  (Homotopy.precomp (StrictSquare.sourceLeg (boundedFlatAffineSectionBassSquare R) ≫
    boundedFlatAffineSectionBassSpanEvaluation R)
    (mappingConeHomotopy (boundedFlatBassSquareComparison R))).cast
      (by apply Hom.ext; funext n; ext x; rfl) rfl

/-- The base evaluation followed by the raw source leg traverses that same cone cylinder. -/
def newCone : Homotopy
    (((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection R)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R)) ≫
          mappingConeInclusion (boundedFlatBassSquareComparison R)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
    boundedFlatBassSourceLeg R) (mappingConeHomotopy (boundedFlatBassSquareComparison R))).cast
      (by apply Hom.ext; funext n; ext x; rfl) rfl

/-- The actual source-leg cone square supplies the whole polynomial-movement boundary. -/
def conePasting :
    (oldCone R).RelHomotopy ((polynomialMovement R).trans (newCone R)) := by
  let Z := Quillen.LoopPrespectrum.Homotopy.refl
    (zeroHom (boundedFlatAffineSectionPrespectrumFunctor.obj R)
      (mappingCone (boundedFlatBassSquareComparison R)))
  have J : (oldCone R).RelHomotopy
      (((polynomialMovement R).trans (newCone R)).trans Z) := by
    refine (boundedFlatAffineSectionBassSourceLegEvaluationConeBoundary R).ofLevels _ _ ?_ ?_
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
    ((positiveMovement R).trans (oldCone R)).RelHomotopy
      ((laurentMovement R).trans ((newPositive R).trans (newCone R))) :=
  ((Homotopy.RelHomotopy.refl (positiveMovement R)).hcomp (conePasting R)).trans
    ((Homotopy.RelHomotopy.transAssoc _ _ _).symm.trans
      (((positivePasting R).hcomp (Homotopy.RelHomotopy.refl (newCone R))).trans
        (Homotopy.RelHomotopy.transAssoc _ _ _)))

/-- The unchanged strict nullhomotopy followed by the actual proved cone evaluation. -/
def originalOldNull : Homotopy
    ((boundedFlatAffineSectionPrespectrumFunctor.map (laurentCoefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (LaurentPolynomial R))) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison R)) (zeroHom _ _) :=
  ((boundedFlatAffineSectionBassNullHomotopy R).postcomp
    (boundedFlatAffineSectionBassConeEvaluation R)).cast
      (by rw [Category.assoc, boundedFlatAffineSectionBassConeEvaluation_inclusion,
        ← Category.assoc])
      (by apply Hom.ext; funext n; ext x
          exact (boundedFlatAffineSectionBassConeEvaluation R).map_point n)

/-- The unchanged raw nullhomotopy preceded by the actual original base evaluation. -/
def originalNewNull : Homotopy
    ((boundedFlatAffineSectionEvaluationPrespectrumMap R ≫
      boundedFlatPerfectPrespectrumMap (laurentProjection R)) ≫
        mappingConeInclusion (boundedFlatBassSquareComparison R)) (zeroHom _ _) :=
  (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatBassLaurentNullHomotopy R)).cast (Category.assoc _ _ _).symm rfl

/-- Every original raw-null coordinate retains its positive track and actual cone cylinder. -/
theorem originalNewNull_level (n : ℕ) :
    (originalNewNull R).level n = ((newPositive R).trans (newCone R)).level n := by
  unfold originalNewNull
  rw [Homotopy.cast_level]
  change ((Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    ((boundedFlatLaurentPlusHomotopy R).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R)))).trans
      (Homotopy.precomp (boundedFlatAffineSectionEvaluationPrespectrumMap R)
        (Homotopy.precomp (boundedFlatBassSourceLeg R)
          (mappingConeHomotopy (boundedFlatBassSquareComparison R))))).level n = _
  apply Homotopy.trans_level_congr <;> rfl

/-- The original strict-null image retains the full comparison track and raw cone coordinate. -/
theorem originalOldNull_level (n : ℕ) :
    (originalOldNull R).level n = ((positiveMovement R).trans (oldCone R)).level n := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  rfl

/-- The unchanged original Laurent nullhomotopies compare along actual Laurent evaluation. -/
def originalNullComparison :
    (originalOldNull R).RelHomotopy ((laurentMovement R).trans (originalNewNull R)) := by
  refine (pastedNullComparison R).ofLevels _ _ (originalOldNull_level R) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact originalNewNull_level R n

end Quillen.PerfectComplexes.SectionBassEvaluationNull
