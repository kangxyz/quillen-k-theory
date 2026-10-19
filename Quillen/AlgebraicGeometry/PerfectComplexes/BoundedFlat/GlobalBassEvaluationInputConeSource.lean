/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputComparisonTracks
public import Quillen.Topology.Prespectrum.ConeSquareMapStrictPrecomposition

/-!
# Literal strict precomposition of the original global evaluation cone map

The original strict square-input map acts on the entire cone without adding a constant half.
Its composite with the original X evaluation is exactly the direct square-cone map of the
specified mixed source track. This identification does not assume a mixed overlap filler.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputConeSource
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original strict square arrow induces its actual commuting comparison-arrow square. -/
def comparisonArrow :
    Arrow.mk (StrictSquare.comparison (sectionSquare Y)) ⟶
      Arrow.mk (StrictSquare.comparison (sectionSquare X)) :=
  strictSquareComparisonFunctor.map
    (GlobalSchemeLaurentTrack.diagram.mapArrow.mapArrow.map (squareFunctor.map g.op))

/-- The strict input is the original cone functor applied to the actual comparison arrow. -/
def strictConeMap : mappingCone (StrictSquare.comparison (sectionSquare Y)) ⟶
    mappingCone (StrictSquare.comparison (sectionSquare X)) :=
  mappingConeMap (comparisonArrow g)

/-- The entire direct square-cone map uses the specified original strict-precomposed track. -/
def directConeMap :=
  mappingConeSquareMap (StrictSquare.comparison (sectionSquare Y)) (GlobalRawBass.comparison X)
    (InputSpan.sectionSpanMap g ≫ spanEvaluation X)
    (sectionMap (laurent.map g) ≫ evaluation (laurent.obj X)) (InputComparisonTracks.source g)

/-- Strict precomposition retains the complete original cone map and its original half-clock. -/
theorem strict_comp_evaluation : strictConeMap g ≫ coneEvaluation X = directConeMap g := by
  exact mappingConeMap_comp_squareMap
    (StrictSquare.comparison (sectionSquare Y)) (StrictSquare.comparison (sectionSquare X))
    (GlobalRawBass.comparison X) (comparisonArrow g) (spanEvaluation X)
    (evaluation (laurent.obj X)) (comparisonHomotopy X)

/-- Original parameter looping preserves this literal whole-map identification. -/
theorem strict_loop_comp_evaluation :
    parameterLoopingMap (strictConeMap g) ≫ stepEvaluation X =
      parameterLoopingMap (directConeMap g) :=
  (parameterLoopingFunctor.map_comp (strictConeMap g) (coneEvaluation X)).symm.trans
    (congrArg parameterLoopingMap (strict_comp_evaluation g))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputConeSource
