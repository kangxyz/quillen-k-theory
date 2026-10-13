/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.LocalConnectorHypotheses
public import Quillen.Topology.Realization.ColimitLocallyPathConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Named regressions for chronological chart algebra, actual projection and local topology. -/
@[expose] public section
noncomputable section
open Set Bundle
universe u v w
namespace QuillenTest.PathClassPrebundle

open Quillen
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  (A : PathThinNeighborhoods X) (b : X)

/-- The fibre coordinate finishes by the reverse chosen path, not the reverse
of the entire based class. -/
theorem forward_coordinate (c y : X) (r : PathClassFiber b y) :
    (A.fiberEquiv b c y r).toQuotient =
      Path.Homotopic.Quotient.trans r.toQuotient (A.chartClass b c y).symm := rfl

/-- The inverse prepends the loop in chronological path notation. -/
theorem inverse_coordinate (c y : X) (g : PathClassFiber b b) :
    ((A.fiberEquiv b c y).symm g).toQuotient =
      Path.Homotopic.Quotient.trans g.toQuotient (A.chartClass b c y) := rfl

/-- The diagonal transition is the genuine constant path class. -/
theorem transition_diagonal (c y : X) :
    (A.transitionClass b c c y).toQuotient = Path.Homotopic.Quotient.refl b := by
  simp [PathThinNeighborhoods.transitionClass]

/-- Chronological composition goes from `e` to `d`, then `d` to `c`. -/
theorem transition_cocycle (c d e y : X) :
    Path.Homotopic.Quotient.trans (A.transitionClass b d e y).toQuotient
        (A.transitionClass b c d y).toQuotient = (A.transitionClass b c e y).toQuotient := by
  change ((A.chartClass b e y).trans (A.chartClass b d y).symm).trans
      ((A.chartClass b d y).trans (A.chartClass b c y).symm) =
    (A.chartClass b e y).trans (A.chartClass b c y).symm
  rw [← Path.Homotopic.Quotient.trans_assoc]
  congr 1
  simp

/-- The actual constructed projection has no missing base fibre. -/
theorem every_fiber_inhabited (y : X) :
    ∃ e : PathThinNeighborhoods.Total b, e.proj = y :=
  PathThinNeighborhoods.projection_surjective b y

/-- A concrete one-point base exercises the geometric hypothesis independently
of a pre-existing covering map. -/
def pointNeighborhoods : PathThinNeighborhoods PUnit where
  neighborhood _ := univ
  isOpen_neighborhood _ := isOpen_univ
  mem_neighborhood _ := mem_univ _
  isPathConnected_neighborhood _ := isPathConnected_univ
  ambientPathThin _ := by
    intro x y p q _ _
    exact SimplyConnectedSpace.paths_homotopic p q

/-- The chart-generated topology gives an actual covering of the one-point base. -/
theorem point_covering :
    letI := (pointNeighborhoods.prebundle PUnit.unit).totalSpaceTopology
    IsCoveringMap (Bundle.TotalSpace.proj :
      PathThinNeighborhoods.Total PUnit.unit → PUnit) :=
  pointNeighborhoods.isCoveringMap_projection PUnit.unit

omit [PathConnectedSpace X] in
/-- The local connector itself supplies both local hypotheses on the original
base, without a CW-type or covering premise. -/
theorem connector_supplies_local_hypotheses (E : LocalEquiconnection X) :
    LocallyPathConnectedSpace X ∧ Nonempty (PathThinNeighborhoods X) :=
  ⟨E.locallyPathConnectedSpace, ⟨E.pathThinNeighborhoods⟩⟩

/-- Every decoded fibre coordinate returns the exact original based path class. -/
theorem coordinate_roundtrip (c y : X) (r : PathClassFiber b y) :
    (A.fiberEquiv b c y).symm (A.fiberEquiv b c y r) = r :=
  (A.fiberEquiv b c y).symm_apply_apply r

end QuillenTest.PathClassPrebundle

open CategoryTheory CategoryTheory.Limits in
/-- The theorem applies to the actual chosen categorical colimit; no topology
transport along a homotopy equivalence enters this interface. -/
theorem QuillenTest.chosen_colimit_local_paths
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u})
    [∀ j, LocallyPathConnectedSpace (F.obj j)] [HasColimit F] :
    LocallyPathConnectedSpace ((colimit F : TopCat.{u}) : Type u) :=
  Quillen.locallyPathConnectedSpace_of_isColimit F (colimit.cocone F) (colimit.isColimit F)
