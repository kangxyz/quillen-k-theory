/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.Basic
public import Quillen.Topology.Realization.Connectivity
public import Quillen.CategoryTheory.TheoremB.CompositionHomotopy
public import Quillen.CategoryTheory.TheoremB.Naturality

/-!
# Coherent coefficient transport along categorical natural transformations

The original realization tracks induce coefficient isomorphisms. Their
composition law uses the proved triangle homotopy, rather than identifying
concatenated paths by fiat.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v

namespace Quillen.LocalCoefficients
/-- Coefficient natural transformations on a classifying space are determined
at actual object vertices, because every point is joined to such a vertex. -/
theorem coefficientMap_ext_vertices {C : Type u} [SmallCategory C]
    {A B : System.{u, v} (ClassifyingSpace C)} {η θ : A ⟶ B}
    (h : ∀ c : C, η.app (FundamentalGroupoid.mk (classifyingSpacePoint c)) =
      θ.app (FundamentalGroupoid.mk (classifyingSpacePoint c))) : η = θ := by
  apply NatTrans.ext
  funext x
  obtain ⟨c, ⟨p⟩⟩ := classifyingSpace_joined_vertex x.as
  apply (cancel_epi (transportIso A p).hom).mp
  change transport A p ≫ η.app (FundamentalGroupoid.mk x.as) =
    transport A p ≫ θ.app (FundamentalGroupoid.mk x.as)
  rw [transport_naturality η p, transport_naturality θ p, h c]

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
    (A : System.{u, v} (ClassifyingSpace D))

/-- Transport along the original realized natural-transformation track. -/
def categoryTrackIso {F G : C ⥤ D} (α : F ⟶ G) :
    pullback (classifyingSpaceMap F).hom A ≅ pullback (classifyingSpaceMap G).hom A :=
  homotopyPullbackIso (classifyingSpaceNaturalTransformationHomotopy α) A

/-- The original composite track gives the composite coefficient conversion. -/
theorem categoryTrackIso_comp {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    categoryTrackIso A (α ≫ β) = categoryTrackIso A α ≪≫ categoryTrackIso A β := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  change transport A ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).evalAt x.as) =
    transport A ((classifyingSpaceNaturalTransformationHomotopy α).evalAt x.as) ≫
      transport A ((classifyingSpaceNaturalTransformationHomotopy β).evalAt x.as)
  rw [transport_eq_of_homotopic A
    ⟨TheoremB.naturalTransformationCompositionPathHomotopy α β x.as⟩, transport_trans]

/-- Identity transformations act identically on coefficients. -/
@[simp]
theorem categoryTrackIso_id (F : C ⥤ D) :
    categoryTrackIso A (𝟙 F) = Iso.refl _ := by
  have h := congrArg Iso.hom (categoryTrackIso_comp A (𝟙 F) (𝟙 F))
  simp only [Category.id_comp, Iso.trans_hom] at h
  apply Iso.ext
  apply (cancel_epi (categoryTrackIso A (𝟙 F)).hom).mp
  simpa using h.symm

/-- The pullback systems and their genuine track transport form an actual functor. -/
def categoryPullbackFunctor : (C ⥤ D) ⥤ (FundamentalGroupoid (ClassifyingSpace C) ⥤
    ModuleCat.{v} ℤ) where
  obj F := pullback (classifyingSpaceMap F).hom A
  map α := (categoryTrackIso A α).hom
  map_id F := by rw [categoryTrackIso_id]; rfl
  map_comp α β := congrArg Iso.hom (categoryTrackIso_comp A α β)

end Quillen.LocalCoefficients
