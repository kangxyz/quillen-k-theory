/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Realization.EdgePathPresentation.SimplicialFullness

/-! Original-vertex and original-cell consumers of generic simplicial graph generation. -/
@[expose] public section

noncomputable section
open CategoryTheory Convexity Quillen
open scoped Simplicial Topology
universe u v w
namespace Quillen.Tests.SimplicialGraphOriginalEdges
variable (X : SSet.{u})

/-- The actual zero-skeleton inverse followed by inclusion gives the original vertex point. -/
theorem original_vertex_round_trip (x : X _⦋0⦌) :
    SSet.toTop.map (X.skeleton 1).ι ((zeroSkeletonHomeomorph X).symm x) =
      realizationPoint x := by
  rw [zeroSkeletonHomeomorph_symm_vertex, zeroSkeletonPoint_inclusion]

/-- An actual one-cell is a loop at its attached vertex exactly when its
original two simplicial face vertices coincide. -/
theorem original_cell_is_loop_iff (a : SimplicialGraph.Index X) :
    SimplicialGraph.inclusion X (SimplicialGraph.characteristic X (a, StdSimplex.single 0)) =
      SimplicialGraph.inclusion X (SimplicialGraph.characteristic X (a, StdSimplex.single 1)) ↔
        X.δ 1 a.simplex = X.δ 0 a.simplex := by
  have hs := SimplicialGraph.characteristic_path X a 0
  have ht := SimplicialGraph.characteristic_path X a 1
  rw [StdSimplex.homeomorphI_symm_zero] at hs
  rw [StdSimplex.homeomorphI_symm_one] at ht
  rw [hs, ht, Path.source, Path.target]
  exact (realizationPoint_injective X).eq_iff

/-- Representing the unchanged original edges represents arbitrary actual
based loop classes, with the originally supplied vertex anchor. -/
theorem original_edge_data_covers_based_loops {A : Type v} [Groupoid.{w} A]
    (F : A ⥤ FundamentalGroupoid |X|) (vertex : X _⦋0⦌ → A)
    (ε : ∀ x, F.obj (vertex x) ≅ FundamentalGroupoid.mk (realizationPoint x))
    (edge : ∀ {x y : X _⦋0⦌}, X.Edge x y → (vertex x ⟶ vertex y))
    (he : ∀ {x y : X _⦋0⦌} (e : X.Edge x y),
      F.map (edge e) = (ε x).hom ≫ ⟦realizationEdgePath e⟧ ≫ (ε y).inv)
    (x : X _⦋0⦌) (p : Path (realizationPoint x) (realizationPoint x)) :
    ∃ g : vertex x ⟶ vertex x, F.map g = (ε x).hom ≫ ⟦p⟧ ≫ (ε x).inv :=
  SimplicialGraph.map_surjective_of_edges X F vertex ε edge he x x _

end Quillen.Tests.SimplicialGraphOriginalEdges
