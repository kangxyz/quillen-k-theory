/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.Homotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Topological cylinders preserve colimits

Product with a locally compact space has the compact-open mapping-space
functor as a right adjoint. In particular, taking product with the interval
preserves the colimits used to construct geometric realization. This is a
proved topological part of the realization-of-homotopies construction; the
standard-simplex prism comparison is proved separately in
`Quillen.RealizationPrismGluing`.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology

universe u w v

namespace Quillen

/-- The compact-open mapping-space functor for a fixed topological space. -/
def topologicalMappingSpace (K : TopCat.{u}) : TopCat.{u} ⥤ TopCat.{u} where
  obj Y := TopCat.of C(K, Y)
  map f := TopCat.ofHom ⟨ContinuousMap.comp f.hom, ContinuousMap.continuous_postcomp _⟩
  map_id Y := by ext g k; rfl
  map_comp f g := by ext h k; rfl

/-- Product with a locally compact space is left adjoint to its compact-open
mapping-space functor. -/
def topologicalProductMappingSpaceAdjunction (K : TopCat.{u}) [LocallyCompactSpace K] :
    tensorRight K ⊣ topologicalMappingSpace K :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦
        { toFun := fun f ↦ TopCat.ofHom f.hom.curry
          invFun := fun f ↦ TopCat.ofHom f.hom.uncurry
          left_inv := fun f ↦ by ext z; rfl
          right_inv := fun f ↦ by ext x k; rfl }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

/-- Topological cylinder formation preserves arbitrary existing colimits. -/
instance topologicalCylinder_preservesColimits :
    PreservesColimitsOfSize.{v, w} (tensorRight TopCat.I.{u}) := by
  let := (topologicalProductMappingSpaceAdjunction TopCat.I.{u}).isLeftAdjoint
  infer_instance

end Quillen
