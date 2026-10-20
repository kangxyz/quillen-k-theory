/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.KTheory.Bass.ConeGeneratorRecognition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedStrictification
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientKOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedCell

/-! Actual returned tensor data instantiate the generator recognition criterion. -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.ReturnedTensorConeRecognition
open GlobalSectionChangeIndex ModelDiagramRowInterchange ParameterTensorEvaluationRow
open GeometricSeedCospan

/-- The input is actual returned tensor multiplication, with its proved evaluation conjugation. -/
def tensorFamily (Q : Scheme.{u}) :=
  ModelUnitRowStrictification.family laurent.op coefficient (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q)

/-- The tensor cell's four-arrow compatibility is proved, not a new hypothesis of recognition. -/
theorem tensorFamily_naturality (Q : Scheme.{u})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((ParameterModels.ambient Q).obj X)).space n) :
    ((DiagramRowRefinement.diagram (ParameterModels.ambient Q ⋙ prespectrumFunctor)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q))).map (laurent.op.map g)).map n
        (((tensorFamily Q).val X).level n (r, x)) =
      ((tensorFamily Q).val Y).level n
        (r, (prespectrumMap ((ParameterModels.ambient Q).map g)).map n x) :=
  (tensorFamily Q).property.1 g n r x


end Quillen.PerfectComplexes.ReturnedTensorConeRecognition
