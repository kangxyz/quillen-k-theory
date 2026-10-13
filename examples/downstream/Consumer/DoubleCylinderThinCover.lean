/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.ThinNeighborhoods
public import Quillen.Topology.Covering.PathClassSimplyConnected

/-! # A genuine cover on the original double cylinder from end thin neighborhoods

The path-class total uses its original prebundle topology.
Neither a cover of the double cylinder nor a map between covers is an input.
-/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
universe u
namespace Consumer.DoubleCylinderThinCover
open Quillen

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
  [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace C]
  [PathConnectedSpace D]

include sq in
/-- The literal connected double cylinder has a constructed simply connected surjective cover. -/
theorem original_double_cylinder_has_cover
    (EB : PathThinNeighborhoods B) (EC : PathThinNeighborhoods C) (d : D) :
    ∃ T : Type u, ∃ tT : TopologicalSpace T,
      let := tT
      ∃ p : C(T, D), IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace T := by
  let := DoubleCylinder.locallyPathConnectedSpace f g sq
  let N := DoubleCylinder.pathThinNeighborhoods f g sq EB EC
  let := (N.prebundle d).totalSpaceTopology
  let T := PathThinNeighborhoods.Total d
  let p : C(T, D) := ⟨Bundle.TotalSpace.proj, (N.isCoveringMap_projection d).continuous⟩
  exact ⟨T, inferInstance, p, N.isCoveringMap_projection d,
    PathThinNeighborhoods.projection_surjective d, N.total_simplyConnectedSpace d⟩

end Consumer.DoubleCylinderThinCover
