/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremB.RowDegeneracies
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting

/-!
# The splitting of the realized simplicial replacement

The Eilenberg–Zilber decomposition of base chains splits each topological
replacement row into the nondegenerate base summands and all their unique
degeneracies. The splitting uses the actual realization topologies.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.TheoremB

/-- A surjective simplex operator preserves the initial vertex. -/
theorem simplex_epi_zero {p q : SimplexCategory} (f : p ⟶ q) [Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (SimplexCategory.epi_iff_surjective.mp (inferInstance : Epi f)) 0
  exact le_antisymm ((f.toOrderHom.monotone (Fin.zero_le k)).trans_eq hk) (Fin.zero_le _)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Every surjective simplex operator induces an isomorphism on a
replacement-row fiber. -/
theorem firstVertexEdge_epi_isIso {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q)
    [Epi α.unop] (s : (nerve D).obj p) : IsIso (TheoremA.firstVertexEdge α s) := by
  change Fin (p.unop.len + 1) ⥤ D at s
  change IsIso (s.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))
  rw [simplex_epi_zero α.unop]
  change IsIso (s.map (𝟙 (0 : Fin (p.unop.len + 1))))
  rw [s.map_id]
  infer_instance

/-- The base map of an iterated degeneracy is injective. -/
theorem nerve_epi_injective {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) [Epi α.unop] :
    Function.Injective ((nerve D).map α) := by
  obtain ⟨⟨hα⟩⟩ := isSplitEpi_of_epi α.unop
  apply Function.LeftInverse.injective (g := (nerve D).map hα.section_.op)
  intro s
  change ((nerve D).map α ≫ (nerve D).map hα.section_.op) s = s
  rw [← (nerve D).map_comp]
  have hid : α ≫ hα.section_.op = 𝟙 p := by
    simpa only [op_comp, Quiver.Hom.op_unop, op_id] using congrArg Quiver.Hom.op hα.id
  rw [hid, (nerve D).map_id]
  rfl

/-- Fiber transitions of an iterated degeneracy are actual homeomorphisms. -/
def epiFiberHomeomorph {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) [Epi α.unop]
    (s : (nerve D).obj p) :
    |H.obj (s.obj 0)| ≃ₜ |H.obj (((nerve D).map α s).obj 0)| := by
  letI := firstVertexEdge_epi_isIso (D := D) α s
  exact TopCat.homeoOfIso (asIso (SSet.toTop.map (H.map (TheoremA.firstVertexEdge α s))))

/-- Iterated degeneracies are open embeddings of genuine topological rows. -/
theorem topologicalRowMap_epi_isOpenEmbedding {p q : SimplexCategoryᵒᵖ}
    (α : p ⟶ q) [Epi α.unop] : Topology.IsOpenEmbedding (topologicalRowMap H α) :=
  sigmaReindexContinuousMap_isOpenEmbedding _ _ (nerve_epi_injective α)
    (fun s ↦ (epiFiberHomeomorph H α s).isOpenEmbedding)

/-- The nondegenerate summands of a replacement row. -/
def nondegenerateTopologicalRow (n : ℕ) : TopCat.{u} :=
  TopCat.of (Σ s : (nerve D).nonDegenerate n, |H.obj (s.1.obj 0)|)

/-- The canonical inclusion of nondegenerate base summands. -/
def nondegenerateTopologicalRowInclusion (n : ℕ) :
    nondegenerateTopologicalRow H n ⟶ (topologicalReplacement H).obj (op ⦋n⦌) :=
  TopCat.ofHom (TheoremA.sigmaSubfamilyInclusion
    (X := fun s : (nerve D).obj (op ⦋n⦌) ↦ |H.obj (s.obj 0)|) ((nerve D).nonDegenerate n))

/-- Inclusion of the nondegenerate summands is an open embedding. -/
theorem nondegenerateTopologicalRowInclusion_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (nondegenerateTopologicalRowInclusion H n) :=
  sigmaReindexContinuousMap_isOpenEmbedding
    (X := fun s : (nerve D).nonDegenerate n ↦ |H.obj (s.1.obj 0)|)
    (Y := fun s : (nerve D).obj (op ⦋n⦌) ↦ |H.obj (s.obj 0)|)
    Subtype.val (fun _ ↦ ContinuousMap.id _) Subtype.val_injective
    (fun _ ↦ (Homeomorph.refl _).isOpenEmbedding)

/-- The canonical map from all unique degeneracies of nondegenerate
summands to the whole row. -/
def topologicalReplacementSplitMap (p : SimplexCategoryᵒᵖ) :
    C((Σ A : SimplicialObject.Splitting.IndexSet p,
      nondegenerateTopologicalRow H A.1.unop.len), (topologicalReplacement H).obj p) :=
  ContinuousMap.sigma fun A ↦
    (topologicalRowMap H A.e.op).comp (nondegenerateTopologicalRowInclusion H A.1.unop.len).hom

/-- The Eilenberg–Zilber decomposition makes the splitting map surjective. -/
theorem topologicalReplacementSplitMap_surjective (p : SimplexCategoryᵒᵖ) :
    Function.Surjective (topologicalReplacementSplitMap H p) := by
  rcases p with ⟨⟨n⟩⟩
  rintro ⟨s, x⟩
  obtain ⟨m, f, hf, t, rfl⟩ := (nerve D).exists_nonDegenerate s
  obtain ⟨y, hy⟩ := (epiFiberHomeomorph H f.op t.1).surjective x
  refine ⟨⟨SimplicialObject.Splitting.IndexSet.mk f, ⟨t, y⟩⟩, ?_⟩
  exact congrArg (Sigma.mk _) hy

/-- Uniqueness of the nondegenerate base presentation, followed by the
homeomorphism on the fiber, makes the splitting map injective. -/
theorem topologicalReplacementSplitMap_injective (p : SimplexCategoryᵒᵖ) :
    Function.Injective (topologicalReplacementSplitMap H p) := by
  rcases p with ⟨⟨n⟩⟩
  rintro ⟨⟨⟨⟨m⟩⟩, f, hf⟩, ⟨s, x⟩⟩ ⟨⟨⟨⟨k⟩⟩, g, hg⟩, ⟨t, y⟩⟩ h
  have hb : (nerve D).map f.op s.1 = (nerve D).map g.op t.1 := congrArg Sigma.fst h
  obtain rfl : m = k := (nerve D).unique_nonDegenerate_dim _ f s rfl g t hb
  obtain rfl : f = g := (nerve D).unique_nonDegenerate_map _ f s rfl g t hb
  obtain rfl : s = t := (nerve D).unique_nonDegenerate_simplex _ f s rfl f t hb
  have hxy : x = y := (epiFiberHomeomorph H f.op s.1).injective
    (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  subst y
  rfl

/-- All summand maps are open, hence the full splitting map is open. -/
theorem topologicalReplacementSplitMap_isOpenMap (p : SimplexCategoryᵒᵖ) :
    IsOpenMap (topologicalReplacementSplitMap H p) := by
  apply isOpenMap_sigma.mpr
  intro A
  exact ((topologicalRowMap_epi_isOpenEmbedding H A.e.op).comp
    (nondegenerateTopologicalRowInclusion_isOpenEmbedding H A.1.unop.len)).isOpenMap

/-- The canonical unique-degeneracy decomposition is a homeomorphism,
not merely a set-theoretic splitting. -/
def topologicalReplacementSplitHomeomorph (p : SimplexCategoryᵒᵖ) :
    (Σ A : SimplicialObject.Splitting.IndexSet p,
      nondegenerateTopologicalRow H A.1.unop.len) ≃ₜ (topologicalReplacement H).obj p :=
  (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (topologicalReplacementSplitMap H p).continuous
    (topologicalReplacementSplitMap_injective H p)
    (topologicalReplacementSplitMap_isOpenMap H p)).isEmbedding.toHomeomorphOfSurjective
      (topologicalReplacementSplitMap_surjective H p)

/-- The topological simplicial replacement is split, with nondegenerate
base-chain summands as its distinguished nondegenerate objects. -/
def topologicalReplacementSplitting : SimplicialObject.Splitting (topologicalReplacement H) where
  N := nondegenerateTopologicalRow H
  ι := nondegenerateTopologicalRowInclusion H
  isColimit' p := by
    let E : TopCat.of (Σ A : SimplicialObject.Splitting.IndexSet p,
        nondegenerateTopologicalRow H A.1.unop.len) ≅ (topologicalReplacement H).obj p :=
      TopCat.isoOfHomeo (topologicalReplacementSplitHomeomorph H p)
    exact IsColimit.ofIsoColimit
      (TopCat.sigmaCofanIsColimit
        (fun A : SimplicialObject.Splitting.IndexSet p ↦
          nondegenerateTopologicalRow H A.1.unop.len))
      (Cofan.ext E (fun _ ↦ rfl))

/-- The actual row realizations inherit this genuine simplicial splitting
through the proved natural row homeomorphisms. -/
def realizedReplacementSplitting :
    SimplicialObject.Splitting (TheoremA.simplicialReplacement H ⋙ SSet.toTop) :=
  (topologicalReplacementSplitting H).ofIso (topologicalReplacementIso H).symm

end Quillen.TheoremB
