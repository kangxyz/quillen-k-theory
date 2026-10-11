/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.DeformationRetract.Basic

/-!
# Gluing coherent diagram homotopies

A natural family of actual cylinder homotopies descends to the actual
topological colimit. Accordingly an equivalence of diagrams whose inverses
and inverse homotopies are coherent gives an actual equivalence of colimits.

This theorem records the coherence needed by an inductive skeletal argument;
it does not infer that coherence from objectwise homotopy equivalences.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u v w

namespace Quillen.TheoremA

variable {J : Type w} [Category.{v} J]

/-- An actual cylinder homotopy natural in the indexing category. -/
structure DiagramCylinderHomotopy {F G : J ⥤ TopCat.{u}} (η θ : F ⟶ G) where
  /-- The natural family of cylinder maps from `F` to `G` whose two endpoint restrictions are `η`
  and `θ`. -/
  h : F ⋙ tensorRight TopCat.I ⟶ G
  h₀ : ∀ j, TopCat.ι₀ ≫ h.app j = η.app j
  h₁ : ∀ j, TopCat.ι₁ ≫ h.app j = θ.app j

/-- Coherent cylinder homotopies descend through actual topological colimits. -/
def colimitDiagramHomotopy {F G : J ⥤ TopCat.{u}}
    {η θ : F ⟶ G} (H : DiagramCylinderHomotopy η θ)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) :
    (hc.map d η).hom.Homotopy (hc.map d θ).hom := by
  let hcI := isColimitOfPreserves (tensorRight TopCat.I) hc
  have hfac (j : J) : (tensorRight TopCat.I).map (c.ι.app j) ≫ hcI.map d H.h =
      H.h.app j ≫ d.ι.app j := hcI.ι_map d H.h j
  refine Quillen.homotopyOfCylinder (hcI.map d H.h) ?_ ?_
  · apply hc.hom_ext
    intro j
    rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc]
    change TopCat.ι₀ ≫ (tensorRight TopCat.I).map (c.ι.app j) ≫ hcI.map d H.h = _
    rw [hfac, ← Category.assoc, H.h₀, hc.ι_map]
  · apply hc.hom_ext
    intro j
    rw [← Category.assoc, ← TopCat.ι₁_comp, Category.assoc]
    change TopCat.ι₁ ≫ (tensorRight TopCat.I).map (c.ι.app j) ≫ hcI.map d H.h = _
    rw [hfac, ← Category.assoc, H.h₁, hc.ι_map]

@[simp]
theorem colimitMap_id {F : J ⥤ TopCat.{u}} (c : Cocone F) (hc : IsColimit c) :
    hc.map c (𝟙 F) = 𝟙 c.pt := by
  apply hc.hom_ext
  intro j
  rw [hc.ι_map]
  simp

theorem colimitMap_comp {F G K : J ⥤ TopCat.{u}}
    (η : F ⟶ G) (θ : G ⟶ K)
    (c : Cocone F) (hc : IsColimit c)
    (d : Cocone G) (hd : IsColimit d) (e : Cocone K) :
    hc.map d η ≫ hd.map e θ = hc.map e (η ≫ θ) := by
  apply hc.hom_ext
  intro j
  rw [← Category.assoc, hc.ι_map, Category.assoc, hd.ι_map, hc.ι_map]
  rfl

/-- A coherent homotopy equivalence of diagrams induces a genuine homotopy
equivalence of their colimits, with the canonical induced forward map. -/
def colimitDiagramHomotopyEquiv {F G : J ⥤ TopCat.{u}}
    (η : F ⟶ G) (θ : G ⟶ F)
    (H : DiagramCylinderHomotopy (η ≫ θ) (𝟙 F))
    (K : DiagramCylinderHomotopy (θ ≫ η) (𝟙 G))
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    ContinuousMap.HomotopyEquiv c.pt d.pt where
  toFun := (hc.map d η).hom
  invFun := (hd.map c θ).hom
  left_inv := by
    have h := colimitDiagramHomotopy H c hc c
    rw [colimitMap_id, ← colimitMap_comp η θ c hc d hd c] at h
    exact ⟨h⟩
  right_inv := by
    have h := colimitDiagramHomotopy K d hd d
    rw [colimitMap_id, ← colimitMap_comp θ η d hd c hc d] at h
    exact ⟨h⟩

@[simp]
theorem colimitDiagramHomotopyEquiv_toFun {F G : J ⥤ TopCat.{u}}
    (η : F ⟶ G) (θ : G ⟶ F)
    (H : DiagramCylinderHomotopy (η ≫ θ) (𝟙 F))
    (K : DiagramCylinderHomotopy (θ ≫ η) (𝟙 G))
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d) :
    (colimitDiagramHomotopyEquiv η θ H K c hc d hd).toFun = (hc.map d η).hom := rfl

end Quillen.TheoremA
