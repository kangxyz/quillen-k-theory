/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluation
public import Quillen.Topology.Prespectrum.StrictSquareNull
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Original source-leg movement under section evaluation

The unchanged polynomial evaluation track moves the actual strict Bass source leg into its raw
geometric counterpart. Interchange with the original cone contraction retains both parameters.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation
open GlobalSectionChangeIndex
variable (X : Scheme.{u})

/-- The original strict Laurent map contracts through its actual positive source-leg cylinder. -/
def strictSourceNull :
    Homotopy (sectionMap (GlobalRawBass.laurentProjection.app X) ≫
      mappingConeInclusion (StrictSquare.comparison (sectionSquare X)))
      (zeroHom (GlobalSchemeLaurentTrack.diagram.obj (Opposite.op X))
        (mappingCone (StrictSquare.comparison (sectionSquare X)))) :=
  (StrictSquare.sourceNullHomotopy (sectionSquare X)).cast
    (by rw [sectionSquare_source]) rfl

/-- Actual span evaluation retains the literal positive polynomial source endpoint. -/
theorem sourceLeg_evaluation :
    StrictSquare.sourceLeg (sectionSquare X) ≫
      spanEvaluation X =
    (sectionMap (projection.app X) ≫
      evaluation (polynomial.obj X)) ≫
        HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The original coefficient homotopy moves the actual source leg through the raw span. -/
def sourceLegHomotopy :
    Homotopy
      (StrictSquare.sourceLeg (sectionSquare X) ≫
        spanEvaluation X)
      (evaluation X ≫ GlobalRawBass.sourceLeg X) :=
  ((evaluationComparison (projection.app X)).postcomp
    (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
      (boundedFlatPerfectPrespectrumMap (projection.app X)))).cast
        (sourceLeg_evaluation X).symm (Category.assoc _ _ _)

/-- The original source-leg movement through the unchanged raw cone nullhomotopy. -/
def sourceLegConeSquare :=
  Homotopy.Square.interchange (sourceLegHomotopy X)
    (mappingConeHomotopy (GlobalRawBass.comparison X))

/-- Both original polynomial and cone parameters remain independent. -/
theorem sourceLegConeSquare_apply (n : ℕ)
    (r s : unitInterval) (x : (GlobalSchemeLaurentTrack.diagram.obj (Opposite.op X)).space n) :
    (sourceLegConeSquare X).level n (r, (s, x)) =
      (mappingConeHomotopy (GlobalRawBass.comparison X)).level n
        (s, (sourceLegHomotopy X).level n (r, x)) := rfl

/-- The actual interchange square supplies its whole pasted boundary. -/
def sourceLegConeBoundary :=
  (sourceLegConeSquare X).toBoundary

end Quillen.PerfectComplexes.GlobalBassEvaluation
