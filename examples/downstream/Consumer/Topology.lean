import Quillen.Topology.Realization.EdgewiseRealization

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u
namespace Consumer

/-- The public edgewise equivalence has the prescribed actual endpoint map. -/
theorem edgewise_forward (X : SSet.{u}) :
    (Quillen.Edgewise.realizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (Quillen.Edgewise.endpoint X)).hom := rfl

/-- Chosen original vertices are preserved through the degenerate interval. -/
theorem edgewise_chosen_vertex (X : SSet.{u}) (x : X _⦋0⦌) :
    Quillen.Edgewise.realizationHomotopyEquiv X
      (Quillen.realizationPoint (Quillen.Edgewise.vertex x)) = Quillen.realizationPoint x :=
  Quillen.Edgewise.realizationHomotopyEquiv_vertex x
end Consumer
