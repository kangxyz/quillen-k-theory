/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.CompositionHomotopy

/-!
# Exact vertex tracks of realized composition coherence

The existing whole-source two-simplex homotopy restricts to an actual homotopy
between the original composite component edge and the concatenation of the
original component edges. The restriction keeps the entire two-parameter family,
not just its endpoints or its homotopy class.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- At a vertex, concatenation keeps the complete parametrizations of both component edges. -/
theorem classifyingHomotopy_trans_vertex {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (c : C) (t : unitInterval) :
    ((classifyingSpaceNaturalTransformationHomotopy α).trans
      (classifyingSpaceNaturalTransformationHomotopy β)) (t, classifyingSpacePoint c) =
      ((classifyingSpacePath (α.app c)).trans (classifyingSpacePath (β.app c))) t := by
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs <;> exact classifyingSpaceNaturalTransformationHomotopy_vertex _ c _

/-- The original composite-arrow edge and original component edges bound the same
full two-parameter homotopy at each object vertex. -/
def naturalTransformationCompositionVertexPathHomotopy {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (c : C) :
    (classifyingSpacePath (α.app c ≫ β.app c)).Homotopy
      ((classifyingSpacePath (α.app c)).trans (classifyingSpacePath (β.app c))) where
  toFun z := naturalTransformationCompositionHomotopy α β (z.1, (z.2, classifyingSpacePoint c))
  continuous_toFun := by fun_prop
  map_zero_left t := ((naturalTransformationCompositionHomotopy α β).map_zero_left
    (t, classifyingSpacePoint c)).trans
      (classifyingSpaceNaturalTransformationHomotopy_vertex (α ≫ β) c t)
  map_one_left t := ((naturalTransformationCompositionHomotopy α β).map_one_left
    (t, classifyingSpacePoint c)).trans (classifyingHomotopy_trans_vertex α β c t)
  prop' s t ht := ((naturalTransformationCompositionHomotopy α β).prop' s
    (t, classifyingSpacePoint c) (by
      rcases ht with ht | ht
      · exact Or.inl ht
      · exact Or.inr (Set.mem_singleton_iff.mp ht))).trans
    (classifyingSpaceNaturalTransformationHomotopy_vertex (α ≫ β) c t)

/-- Restriction to vertices does not alter any point of the two-parameter family. -/
@[simp]
theorem naturalTransformationCompositionVertexPathHomotopy_apply {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (c : C) (s t : unitInterval) :
    naturalTransformationCompositionVertexPathHomotopy α β c (s, t) =
      naturalTransformationCompositionHomotopy α β (s, (t, classifyingSpacePoint c)) := rfl

end Quillen.TheoremB
