/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.KProjectiveRepresentatives
public import Quillen.Algebra.Homology.HomotopyPushoutQuasiIso

/-! # Genuine derived null-detection and the affine term-bound leaf -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
universe u v w
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Disjoint original term supports force every actual derived map to vanish
when the source is genuinely K-projective. -/
theorem derivedHom_eq_zero_of_disjoint_terms
    (K L : CochainComplex C ℤ) [K.IsKProjective]
    (h : ∀ n, IsZero (K.X n) ∨ IsZero (L.X n))
    (φ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) : φ = 0 := by
  obtain ⟨f, rfl⟩ := exists_chain_representative_of_isKProjective φ
  have hf : f = 0 := by
    ext n
    rcases h n with hn | hn
    · exact hn.eq_of_src _ _
    · exact hn.eq_of_tgt _ _
  rw [hf, Functor.map_zero]

/-- A single strictly below a K-projective source's lower term bound receives
no original derived morphisms. No projectivity of the single object is used. -/
theorem derivedHom_single_eq_zero_of_lower_terms
    (K : CochainComplex C ℤ) [K.IsKProjective] (M : C) (a b : ℤ)
    (hK : ∀ n, n < b → IsZero (K.X n)) (hab : a < b)
    (φ : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C a).obj M)) : φ = 0 := by
  apply derivedHom_eq_zero_of_disjoint_terms K _ _ φ
  intro n
  by_cases hn : n = a
  · exact Or.inl (hK n (hn ▸ hab))
  · exact Or.inr (HomologicalComplex.isZero_single_obj_X (.up ℤ) a M n hn)

/-- The actual two original homotopy-pushout inclusions detect a derived map
provided maps from the shifted original overlap vanish. The shift is essential. -/
theorem derivedHom_homotopyPushout_eq_zero
    {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)
    {L : DerivedCategory C}
    (hT : ∀ γ : (DerivedCategory.Q.obj T)⟦(1 : ℤ)⟧ ⟶ L, γ = 0)
    (φ : DerivedCategory.Q.obj (homotopyPushout f g) ⟶ L)
    (hA : DerivedCategory.Q.map (homotopyPushoutInl f g) ≫ φ = 0)
    (hB : DerivedCategory.Q.map (homotopyPushoutInr f g) ≫ φ = 0) : φ = 0 := by
  let d := biprod.lift f (-g)
  have hm : DerivedCategory.Q.map (CochainComplex.mappingCone.inr d) ≫ φ = 0 := by
    have he : (biprod.fst : A ⊞ B ⟶ A) ≫ homotopyPushoutInl f g +
        (biprod.snd : A ⊞ B ⟶ B) ≫ homotopyPushoutInr f g =
        CochainComplex.mappingCone.inr d := by
      simp only [homotopyPushoutInl, homotopyPushoutInr, ← Category.assoc,
        ← Preadditive.add_comp, biprod.total, Category.id_comp, d]
    rw [← he, Functor.map_add, Preadditive.add_comp, Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc, hA, hB, comp_zero, comp_zero, add_zero]
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ _
    (DerivedCategory.mappingCone_triangle_distinguished d) φ hm
  rw [hγ, hT γ, comp_zero]

end Quillen.CochainComplex
