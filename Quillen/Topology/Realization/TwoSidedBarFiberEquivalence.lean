import Quillen.Topology.Realization.TwoSidedBarFiber
import Quillen.Topology.HomotopyFiber.WeakSquareTransport

/-! # The original bar augmentations are weak equivalences on actual fibers

Both maps in the bar zigzag retain their original source coordinates and
postcomposed paths. Genuine homotopy equivalences on total and base spaces,
combined with the proved weak strict-square transport theorem, give the
complete empty-aware weak property. Every finite homotopy set, including
components, is covered without a Whitehead upgrade.
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

/-- The actual coordinate-dropping augmentation gives the complete weak
homotopy equivalence on original fibers, including empty-space cases. -/
theorem dropFiberMap_isWeakHomotopyEquivalence (y : |diagonalSSet (bar J)|) :
    IsWeakHomotopyEquivalence (dropFiberMap η y) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence_of_equivalences
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram H))
    (dropRealizationHomotopyEquiv indexProjection (liftedDiagram J))
    (realizedDropSquare η) y

/-- The actual evaluation augmentation gives the complete weak homotopy
equivalence to the unchanged original diagonal fiber. -/
theorem evaluationFiberMap_isWeakHomotopyEquivalence (y : |diagonalSSet (bar J)|) :
    IsWeakHomotopyEquivalence (evaluationFiberMap η y) :=
  HomotopyFiber.map_isWeakHomotopyEquivalence_of_equivalences
    (evaluationRealizationHomotopyEquiv H) (evaluationRealizationHomotopyEquiv J)
    (realizedEvaluationSquare η) y

/-- Every original finite based drop map is a bijection, including n = 0. -/
theorem dropFiberMap_bijective (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (dropFiberMap η y) (x := p) rfl) :=
  (dropFiberMap_isWeakHomotopyEquivalence η y).homotopy_bijective p n

/-- Every original finite based evaluation map is a bijection, including n = 0. -/
theorem evaluationFiberMap_bijective (y : |diagonalSSet (bar J)|)
    (p : HomotopyFiber (SSet.toTop.map (barMap η)).hom y) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (evaluationFiberMap η y) (x := p) rfl) :=
  (evaluationFiberMap_isWeakHomotopyEquivalence η y).homotopy_bijective p n

end Quillen.TwoSidedBar
