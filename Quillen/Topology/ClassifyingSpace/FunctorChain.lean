/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.TheoremB.StructuredIsoHomotopy

/-! Naturality and fixed-vertex coherence for realized functor chains. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.TheoremB
variable {B C D : Type u} [SmallCategory B] [SmallCategory C] [SmallCategory D]

/-- Restricting the source of a functor chain commutes with its nerve cylinder. -/
theorem functorChainNerveCylinder_whiskerLeft {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (G : B ⥤ C) :
    (nerveMap G ⊗ₘ 𝟙 Δ[n]) ≫ functorChainNerveCylinder A =
      functorChainNerveCylinder (A ⋙ (Functor.whiskeringLeft B C D).obj G) := by
  ext k z
  rfl

/-- Joint simplex realization is natural in the source functor. -/
theorem functorChainRealization_whiskerLeft {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (G : B ⥤ C)
    (x : ClassifyingSpace B) (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization A (classifyingSpaceMap G x, z) =
      functorChainRealization (A ⋙ (Functor.whiskeringLeft B C D).obj G) (x, z) := by
  have hn := realizationProductSimplexIso_inv_naturality (nerveMap G) (𝟙 ⦋n⦌)
  rw [show SSet.stdSimplex.map (𝟙 ⦋n⦌) = 𝟙 (Δ[n] : SSet.{u}) from
    CategoryTheory.Functor.map_id _ _, SSet.toTop.map_id] at hn
  have hv := ConcreteCategory.congr_hom hn (x, z)
  change SSet.toTop.map (functorChainNerveCylinder A)
    ((realizationProductSimplexIso (nerve C) n).inv (classifyingSpaceMap G x, z)) = _
  have hp : (SSet.toTop.map (nerveMap G) ⊗ₘ 𝟙 |(Δ[n] : SSet.{u})|) (x, z) =
      (classifyingSpaceMap G x, z) := rfl
  rw [TopCat.comp_app, TopCat.comp_app, hp] at hv
  rw [← hv]
  change (SSet.toTop.map (nerveMap G ⊗ₘ 𝟙 Δ[n]) ≫
    SSet.toTop.map (functorChainNerveCylinder A)) _ = _
  rw [← SSet.toTop.map_comp, functorChainNerveCylinder_whiskerLeft]
  rfl

theorem functorChainNerveCylinder_const (F : C ⥤ D) (n : ℕ) :
    functorChainNerveCylinder ((Functor.const (Fin (n + 1))).obj F) =
      fst (nerve C) Δ[n] ≫ nerveMap F := by
  ext k z : 4
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    Functor.uncurry.obj ((Functor.const (Fin (n + 1))).obj F) = z.1 ⋙ F
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i; rfl
  · intro i j f
    simp [Functor.uncurry]

theorem functorChainRealization_const (F : C ⥤ D) (n : ℕ)
    (x : ClassifyingSpace C) (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization ((Functor.const (Fin (n + 1))).obj F) (x, z) =
      classifyingSpaceMap F x := by
  change SSet.toTop.map (functorChainNerveCylinder _)
    ((realizationProductSimplexIso (nerve C) n).inv (x, z)) = _
  rw [functorChainNerveCylinder_const, SSet.toTop.map_comp, TopCat.comp_app]
  have hp := congrArg Prod.fst (ConcreteCategory.congr_hom
    (realizationProductSimplexIso (nerve C) n).inv_hom_id (x, z))
  exact congrArg (classifyingSpaceMap F) hp

/-- A chain fixes a vertex whenever all its values there are the same object
and every arrow into that object is unique. This applies to the zero Q-object. -/
theorem functorChainRealization_vertex_of_subsingleton {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (c : C) (d : D)
    (hobj : ∀ i, (A.obj i).obj c = d) (hthin : ∀ Y : D, Subsingleton (Y ⟶ d))
    (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization A (classifyingSpacePoint c, z) = classifyingSpacePoint d := by
  let K := (Functor.const C).obj c
  have he (i : Fin (n + 1)) : K ⋙ A.obj i = (Functor.const C).obj d := by
    refine CategoryTheory.Functor.ext (fun _ ↦ hobj i) ?_
    intro X Y f
    have ht : Subsingleton ((A.obj i).obj c ⟶ (A.obj i).obj c) := by
      rw [hobj i]; exact hthin _
    exact ht.elim _ _
  have hA : A ⋙ (Functor.whiskeringLeft C C D).obj K =
      (Functor.const (Fin (n + 1))).obj ((Functor.const C).obj d) := by
    refine CategoryTheory.Functor.ext he ?_
    intro i j f
    apply NatTrans.ext
    funext X
    have ht : Subsingleton ((A.obj i).obj c ⟶ (A.obj j).obj c) := by
      rw [hobj j]; exact hthin _
    exact ht.elim _ _
  have h := functorChainRealization_whiskerLeft A K (classifyingSpacePoint c) z
  rw [classifyingSpaceMap_point, hA, functorChainRealization_const,
    classifyingSpaceMap_point] at h
  exact h

/-- The inverse-isomorphism coherence really fixes a vertex under the thin
zero-target condition; this is stronger than merely fixing the path endpoints. -/
theorem naturalIsoInverseHomotopy_vertex_of_subsingleton {F G : C ⥤ D}
    (e : F ≅ G) (c : C) (d : D) (hF : F.obj c = d) (hG : G.obj c = d)
    (hthin : ∀ Y : D, Subsingleton (Y ⟶ d)) (s t : unitInterval) :
    naturalIsoInverseHomotopy e (s, (t, classifyingSpacePoint c)) = classifyingSpacePoint d := by
  change functorChainRealization (ComposableArrows.mk₂ e.hom e.inv)
    (classifyingSpacePoint c,
      (SimplexCategory.toTopHomeo ⦋2⦌).symm (inverseTriangleParameter s t)) = _
  apply functorChainRealization_vertex_of_subsingleton _ c d _ hthin
  intro i
  fin_cases i
  · exact hF
  · exact hG
  · exact hF

end Quillen.TheoremB
