/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnitPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-!
# Original global Bass source-null and Laurent-seed compatibility

The independently proved original unit square combines with the full original source-null
pasting. Their actual conjugates compare the one-step strict-section and raw Laurent seeds,
retaining independent comparison, loop and structure coordinates. This is one step only.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation
open GlobalSectionChangeIndex GlobalBassEvaluationNull
variable (X : Scheme.{u})

/-- The original global Laurent-unit seed uses its actual strict source-null cylinder. -/
def strictSeed : GlobalSchemeLaurentTrack.diagram.obj (op X) ⟶
    parameterLooping (mappingCone (StrictSquare.comparison (sectionSquare X))) :=
  ((GlobalSchemeLaurentTrack.homotopy (op X)).postcomp
    (mappingConeInclusion (StrictSquare.comparison (sectionSquare X)))).nullLoopMap
      (strictSourceNull X)

/-- The source is the existing whole-word geometric seed, with no replacement null or unit. -/
theorem strictSeed_eq_wholeSeed :
    strictSeed X =
      (Quillen.KTheory.Bass.WholeSeedCospan.seed
        (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare
          GlobalSchemeLaurentTrack.diagram)
        (Quillen.KTheory.Bass.GeometricSeedCospan.sourceTrack
          GlobalSchemeLaurentTrack.diagram GlobalSchemeLaurentTrack.homotopy)
        (Quillen.KTheory.Bass.GeometricSeedCospan.sourceTrack_naturality
          GlobalSchemeLaurentTrack.diagram GlobalSchemeLaurentTrack.homotopy
          GlobalSchemeLaurentTrack.homotopy_naturality)).app (op X) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  rfl

/-- The original strict unit evaluated into the actual raw cone. -/
def oldUnit :=
  (evaluationOldUnit (GlobalRawBass.laurentProjection.app X)
    (GlobalSchemeLaurentTrack.laurentScalar (op X))).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))

/-- Original base evaluation followed by the original raw forward unit in the same cone. -/
def newUnit :=
  (evaluationNewUnit (GlobalRawBass.laurentProjection.app X)
    (GlobalSchemeLaurentTrack.laurentScalar (op X))).postcomp
      (mappingConeInclusion (GlobalRawBass.comparison X))

/-- The independently constructed unit pasting retains both complete original cone-unit tracks. -/
def unitPasting :
    ((oldUnit X).trans (laurentMovement X)).RelHomotopy
      ((laurentMovement X).trans (newUnit X)) := by
  apply ((globalLaurentEvaluationPasting (op X)).postcomp
    (mappingConeInclusion (GlobalRawBass.comparison X))).ofLevels
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl
  · intro n
    rw [Homotopy.postcomp_trans]
    rfl

/-- Original unit and source-null pastings compare the actual based Laurent conjugates. -/
def conjugation :
    ((oldUnit X).conjugateToZero (originalOldNull X)).RelHomotopy
      ((newUnit X).conjugateToZero (originalNewNull X)) :=
  Homotopy.RelHomotopy.conjugateNaturality (laurentMovement X)
    (oldUnit X) (newUnit X) (originalOldNull X) (originalNewNull X)
    (unitPasting X) (originalNullComparison X)

/-- The initial conjugate is precisely the original strict seed followed by actual evaluation. -/
theorem originalStrictSeed :
    (oldUnit X).nullLoopMap (originalOldNull X) = strictSeed X ≫ stepEvaluation X := by
  have h := Homotopy.nullLoopMap_naturality
    (𝟙 (GlobalSchemeLaurentTrack.diagram.obj (op X))) (coneEvaluation X)
    ((GlobalSchemeLaurentTrack.homotopy (op X)).postcomp
      (mappingConeInclusion (StrictSquare.comparison (sectionSquare X))))
    (oldUnit X) (strictSourceNull X) (originalOldNull X)
    (by intro n; rfl) (by intro n; rfl)
  exact h.symm

/-- The final conjugate is precisely evaluation followed by the unchanged raw Laurent seed. -/
theorem originalRawSeed :
    (newUnit X).nullLoopMap (originalNewNull X) = evaluation X ≫ GlobalRawBass.transition X := by
  have h := Homotopy.nullLoopMap_naturality (evaluation X)
    (𝟙 (mappingCone (GlobalRawBass.comparison X))) (newUnit X)
    ((GlobalRawBass.unitHomotopy X).postcomp (mappingConeInclusion (GlobalRawBass.comparison X)))
    (originalNewNull X) (GlobalRawBass.sourceNull X)
    (by intro n; rfl) (by intro n; rfl)
  exact h

/-- The actual one-step evaluation intertwines the two original forward Laurent seeds. -/
def seedHomotopy : Homotopy (strictSeed X ≫ stepEvaluation X)
    (evaluation X ≫ GlobalRawBass.transition X) :=
  (conjugation X).zeroLoopMapHomotopy.cast (originalStrictSeed X) (originalRawSeed X)

/-- Comparison and output-loop times remain independent at every original source point. -/
theorem seedHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    Path.toContinuousMap ((seedHomotopy X).level n (r, x)) s =
      (conjugation X).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes.GlobalBassEvaluation
