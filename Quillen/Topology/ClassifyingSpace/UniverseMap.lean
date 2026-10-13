/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.UniverseLift

/-!
# Classifying-space maps without universe restrictions

Every functor induces a continuous map between the original geometric
realizations of its source and target nerves, even when their object and
morphism universes differ. The map preserves every simplex coordinate and
object vertex, agrees with ordinary realization when the universes agree,
and respects identities and composition.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace Quillen

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- Postcompose each original nerve simplex with a functor, in arbitrary universes. -/
def nerveUniverseMap (F : C ⥤ D) : SimplicialUniverseMap (nerve C) (nerve D) where
  app _ x := x ⋙ F
  naturality _ _ := rfl

/-- The continuous map of original classifying spaces induced by a functor in any universes. -/
def classifyingSpaceMapUniversal (F : C ⥤ D) :
    C(ClassifyingSpace C, ClassifyingSpace D) :=
  realizationUniverseMap (nerveUniverseMap F)

@[simp] theorem classifyingSpaceMapUniversal_simplex (F : C ⥤ D)
    (n : SimplexCategory) (x : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    classifyingSpaceMapUniversal F (realizationSimplex x t) =
      realizationSimplex (x ⋙ F) t :=
  realizationUniverseMap_simplex _ _ _ _

/-- The map preserves the original object vertices exactly. -/
@[simp] theorem classifyingSpaceMapUniversal_point (F : C ⥤ D) (c : C) :
    classifyingSpaceMapUniversal F (classifyingSpacePoint c) =
      classifyingSpacePoint (F.obj c) := by
  change realizationUniverseMap (nerveUniverseMap F) (realizationPoint (nerveVertex c)) = _
  rw [realizationUniverseMap_point]
  have h : (nerveUniverseMap F).app (op ⦋0⦌) (nerveVertex c) =
      nerveVertex (F.obj c) := by
    exact ComposableArrows.ext₀ rfl
  rw [h]
  rfl

theorem classifyingSpaceMapUniversal_id :
    classifyingSpaceMapUniversal (𝟭 C) = ContinuousMap.id (ClassifyingSpace C) := by
  exact realizationUniverseMap_id (nerve C)

@[simp] theorem classifyingSpaceMapUniversal_comp (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMapUniversal (F ⋙ G) =
      (classifyingSpaceMapUniversal G).comp (classifyingSpaceMapUniversal F) := by
  exact realizationUniverseMap_comp (nerveUniverseMap F) (nerveUniverseMap G)

/-- In common universes, the general map equals the existing classifying-space map. -/
@[simp] theorem classifyingSpaceMapUniversal_eq {C D : Type u₁}
    [Category.{v₁} C] [Category.{v₁} D] (F : C ⥤ D) :
    classifyingSpaceMapUniversal F = (classifyingSpaceMap F).hom := by
  exact realizationUniverseMap_ofHom (nerveMap F)

end Quillen
