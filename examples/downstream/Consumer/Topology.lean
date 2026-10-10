/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.EdgewiseRealization

/-!
# Edgewise realization comparison examples

Identifies the forward map of the public edgewise realization homotopy
equivalence with realization of the endpoint map. The vertex statement records
its action on a specified original vertex.
-/

@[expose] public section

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
