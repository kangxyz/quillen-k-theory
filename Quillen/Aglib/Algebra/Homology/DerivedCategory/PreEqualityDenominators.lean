/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Homology.DerivedCategory.EqualityDenominators

/-! # Genuine pre-quasi-isomorphism homotopy denominators -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Original derived equality admits an actual source denominator and chain homotopy. -/
lemma exists_pre_quasiIso_homotopy_of_derived_eq
    {K L : CochainComplex C ℤ} (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    ∃ (M : CochainComplex C ℤ) (s : M ⟶ K), QuasiIso s ∧ Nonempty (Homotopy (s ≫ f) (s ≫ g)) := by
  let H := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  have he : DerivedCategory.Qh.map (H.map f) = DerivedCategory.Qh.map (H.map g) := by
    have hf := NatIso.naturality_2 e f
    have hg := NatIso.naturality_2 e g
    exact hf.symm.trans ((congrArg (fun t => e.hom.app K ≫ t ≫ e.inv.app L) h).trans hg)
  obtain ⟨M, s, hs, heq⟩ := (MorphismProperty.map_eq_iff_precomp DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ)) (H.map f) (H.map g)).mp he
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨s, rfl⟩ := H.map_surjective s
  refine ⟨M, s, ?_, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  · exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).mp hs
  · simpa only [Functor.map_comp] using heq

/-- Two original equalities admit one common actual source denominator. -/
lemma exists_pre_quasiIso_two_homotopies_of_derived_eq
    {K L₁ L₂ : CochainComplex C ℤ} (f₁ g₁ : K ⟶ L₁) (f₂ g₂ : K ⟶ L₂)
    (h₁ : DerivedCategory.Q.map f₁ = DerivedCategory.Q.map g₁)
    (h₂ : DerivedCategory.Q.map f₂ = DerivedCategory.Q.map g₂) :
    ∃ (M : CochainComplex C ℤ) (s : M ⟶ K), QuasiIso s ∧
      Nonempty (Homotopy (s ≫ f₁) (s ≫ g₁)) ∧ Nonempty (Homotopy (s ≫ f₂) (s ≫ g₂)) := by
  obtain ⟨M₁, s₁, hs₁, ⟨H₁⟩⟩ := exists_pre_quasiIso_homotopy_of_derived_eq f₁ g₁ h₁
  have he₂ : DerivedCategory.Q.map (s₁ ≫ f₂) = DerivedCategory.Q.map (s₁ ≫ g₂) := by
    simp only [Functor.map_comp, h₂]
  obtain ⟨M₂, s₂, hs₂, ⟨H₂⟩⟩ := exists_pre_quasiIso_homotopy_of_derived_eq _ _ he₂
  refine ⟨M₂, s₂ ≫ s₁, inferInstance, ⟨?_⟩, ⟨?_⟩⟩
  · simpa only [Category.assoc] using H₁.compLeft s₂
  · simpa only [Category.assoc] using H₂

/-- A specified original derived isomorphism and target compatibility give
actual weak overlap legs and a chain homotopy, retaining that exact derived isomorphism. -/
lemma exists_weak_span_homotopy_of_derived_iso
    {A B T : CochainComplex C ℤ}
    (e : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B)
    (p : A ⟶ T) (q : B ⟶ T)
    (hpq : DerivedCategory.Q.map p = e.hom ≫ DerivedCategory.Q.map q) :
    ∃ (K : CochainComplex C ℤ) (a : K ⟶ A) (b : K ⟶ B),
      QuasiIso a ∧ QuasiIso b ∧
      DerivedCategory.Q.map a ≫ e.hom = DerivedCategory.Q.map b ∧
      Nonempty (Homotopy (a ≫ p) (b ≫ q)) := by
  obtain ⟨M, s, hs, t, he⟩ := DerivedCategory.right_fac e.hom
  let := hs
  have hs' : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso C s).mp hs
  have hst : DerivedCategory.Q.map s ≫ e.hom = DerivedCategory.Q.map t := by
    rw [he, IsIso.hom_inv_id_assoc]
  have ht : QuasiIso t := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso C t).mp
    rw [← hst]
    infer_instance
  have heq : DerivedCategory.Q.map (s ≫ p) = DerivedCategory.Q.map (t ≫ q) := by
    rw [Functor.map_comp, hpq, ← Category.assoc, hst, Functor.map_comp]
  obtain ⟨K, z, hz, ⟨H⟩⟩ := exists_pre_quasiIso_homotopy_of_derived_eq _ _ heq
  refine ⟨K, z ≫ s, z ≫ t, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · simp only [Functor.map_comp, Category.assoc, hst]
  · simpa only [Category.assoc] using H

end Quillen.CochainComplex
