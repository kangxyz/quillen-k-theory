/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy
public import Quillen.Topology.ClassifyingSpace.NaturalTransformationTracks

/-!
# Original vertex tracks across categorical universes

The actual universe-lifted natural-transformation homotopy traces the original
component edge. Its moving-basepoint formula therefore retains that precise
path, even when the two categories have different object or morphism universes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u₁ v₁ u₂ v₂
open CategoryTheory
namespace Quillen
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Universe lifting preserves the full parametrized component-edge track. -/
theorem classifyingSpaceUniversalHomotopy_vertex_track
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t := by
  change classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D)
    (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C)
        (Functor.whiskerRight α AsSmall.up))
      (t, classifyingSpaceMapUniversal AsSmall.up (classifyingSpacePoint c))) = _
  rw [classifyingSpaceMapUniversal_point,
    classifyingSpaceNaturalTransformationHomotopy_vertex_track,
    classifyingSpaceMapUniversal_path]
  rfl

/-- The original component edge is the exact change of basepoint in every degree. -/
theorem pathTransport_classifyingSpaceMapUniversal_naturalTransformation
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpacePath (α.app c)) n
      (homotopyGroupMap (classifyingSpaceMapUniversal F)
        (classifyingSpaceMapUniversal_point F c) a) =
      homotopyGroupMap (classifyingSpaceMapUniversal G)
        (classifyingSpaceMapUniversal_point G c) a := by
  have ht : ((classifyingSpaceUniversalHomotopy α).evalAt (classifyingSpacePoint c)).cast
      (classifyingSpaceMapUniversal_point F c).symm
      (classifyingSpaceMapUniversal_point G c).symm =
      classifyingSpacePath (α.app c) := by
    ext t
    exact classifyingSpaceUniversalHomotopy_vertex_track α c t
  rw [← ht]
  exact pathTransport_homotopyGroupMap_homotopy_cast
    (classifyingSpaceUniversalHomotopy α) (classifyingSpacePoint c)
    (classifyingSpaceMapUniversal_point F c) (classifyingSpaceMapUniversal_point G c) n a

end Quillen
