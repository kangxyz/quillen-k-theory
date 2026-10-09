import Quillen.Topology.Realization.TwoSidedBarFiber
import Quillen.Topology.HomotopyFiber.SquareEquivalence

/-! # Genuine equivalences for the original two-sided-bar fiber augmentations

Both total and base augmentations have proved genuine homotopy equivalences.
The genuine square-fiber theorem therefore provides actual continuous inverse
maps and inverse homotopies for the original fiber augmentations, retaining
their literal source and complete path coordinates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace Quillen.TwoSidedBar
open TheoremA
variable {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J)

/-- The original drop augmentation is a genuine equivalence on actual fibers. -/
def dropFiberHomotopyEquiv (y : |diagonalSSet (bar J)|) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)
      (HomotopyFiber (SSet.toTop.map (replacementMap η)).hom (SSet.toTop.map (dropMap J) y)) :=
  HomotopyFiber.mapHomotopyEquivOfEquivalences
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram H))
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram J))
    (realizedDropSquare η) y

@[simp] theorem dropFiberHomotopyEquiv_toFun (y : |diagonalSSet (bar J)|) :
    (dropFiberHomotopyEquiv η y).toFun = dropFiberMap η y := rfl

/-- The original evaluation augmentation is a genuine equivalence to the
unchanged original diagonal fiber. -/
def evaluationFiberHomotopyEquiv (y : |diagonalSSet (bar J)|) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (SSet.toTop.map (barMap η)).hom y)
      (HomotopyFiber (SSet.toTop.map (diagonalMap η)).hom (SSet.toTop.map (evaluationMap J) y)) :=
  HomotopyFiber.mapHomotopyEquivOfEquivalences
    (evaluationRealizationHomotopyEquiv H) (evaluationRealizationHomotopyEquiv J)
    (realizedEvaluationSquare η) y

@[simp] theorem evaluationFiberHomotopyEquiv_toFun (y : |diagonalSSet (bar J)|) :
    (evaluationFiberHomotopyEquiv η y).toFun = evaluationFiberMap η y := rfl

end Quillen.TwoSidedBar
