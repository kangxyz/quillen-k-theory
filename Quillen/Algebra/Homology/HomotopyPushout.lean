/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.CategoryTheory.Abelian.Basic

/-! # Actual homotopy pushouts and strict descent equations -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)

/-- The actual cone of the overlap difference map. -/
def homotopyPushout : CochainComplex C ℤ :=
  CochainComplex.mappingCone (biprod.lift f (-g))

/-- Original first summand inclusion. -/
def homotopyPushoutInl : A ⟶ homotopyPushout f g :=
  biprod.inl ≫ CochainComplex.mappingCone.inr (biprod.lift f (-g))

/-- Original second summand inclusion. -/
def homotopyPushoutInr : B ⟶ homotopyPushout f g :=
  biprod.inr ≫ CochainComplex.mappingCone.inr (biprod.lift f (-g))

/-- A specified original overlap homotopy supplies an actual chain descent map. -/
def homotopyPushoutDesc {M : CochainComplex C ℤ} (a : A ⟶ M) (b : B ⟶ M)
    (H : Homotopy (f ≫ a) (g ≫ b)) : homotopyPushout f g ⟶ M :=
  CochainComplex.mappingCone.desc (biprod.lift f (-g)) (Cochain.ofHomotopy H)
    (biprod.desc a b) (by
      rw [δ_ofHomotopy, biprod.lift_desc]
      simp only [Preadditive.neg_comp, ← sub_eq_add_neg, Cochain.ofHom_sub])

@[reassoc (attr := simp)]
lemma homotopyPushoutInl_desc {M : CochainComplex C ℤ} (a : A ⟶ M) (b : B ⟶ M)
    (H : Homotopy (f ≫ a) (g ≫ b)) :
    homotopyPushoutInl f g ≫ homotopyPushoutDesc f g a b H = a := by
  simp [homotopyPushoutInl, homotopyPushoutDesc, Category.assoc]

@[reassoc (attr := simp)]
lemma homotopyPushoutInr_desc {M : CochainComplex C ℤ} (a : A ⟶ M) (b : B ⟶ M)
    (H : Homotopy (f ≫ a) (g ≫ b)) :
    homotopyPushoutInr f g ≫ homotopyPushoutDesc f g a b H = b := by
  simp [homotopyPushoutInr, homotopyPushoutDesc, Category.assoc]

/-- The actual first inclusion is split monic in each original degree. -/
def homotopyPushoutInlSplitMono (i : ℤ) : SplitMono ((homotopyPushoutInl f g).f i) where
  retraction := (CochainComplex.mappingCone.snd (biprod.lift f (-g))).v i i (add_zero i) ≫
    (biprod.fst : A ⊞ B ⟶ A).f i
  id := by
    simp only [homotopyPushoutInl, HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_snd_v_assoc]
    change (biprod.inl ≫ biprod.fst : A ⟶ A).f i = 𝟙 _
    simp

/-- The actual second inclusion is split monic in each original degree. -/
def homotopyPushoutInrSplitMono (i : ℤ) : SplitMono ((homotopyPushoutInr f g).f i) where
  retraction := (CochainComplex.mappingCone.snd (biprod.lift f (-g))).v i i (add_zero i) ≫
    (biprod.snd : A ⊞ B ⟶ B).f i
  id := by
    simp only [homotopyPushoutInr, HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_snd_v_assoc]
    change (biprod.inr ≫ biprod.snd : B ⟶ B).f i = 𝟙 _
    simp

/-- The original mapping cone has its actual canonical null homotopy. -/
def mappingConeCompHomotopy {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    Homotopy (φ ≫ CochainComplex.mappingCone.inr φ) 0 :=
  (Cochain.equivHomotopy _ _).symm ⟨CochainComplex.mappingCone.inl φ, by
    simp only [CochainComplex.mappingCone.δ_inl, Cochain.ofHom_zero, add_zero]⟩

/-- The two original legs agree by the displayed cone homotopy. -/
def homotopyPushoutInclusionHomotopy :
    Homotopy (f ≫ homotopyPushoutInl f g) (g ≫ homotopyPushoutInr f g) := by
  have he : (f ≫ homotopyPushoutInl f g) - (g ≫ homotopyPushoutInr f g) =
      biprod.lift f (-g) ≫ CochainComplex.mappingCone.inr (biprod.lift f (-g)) := by
    simp only [homotopyPushoutInl, homotopyPushoutInr, ← Category.assoc]
    rw [← Preadditive.sub_comp]
    congr 1
    apply biprod.hom_ext <;> simp [Preadditive.sub_comp]
  exact Homotopy.equivSubZero.symm
    ((Homotopy.ofEq he).trans (mappingConeCompHomotopy (biprod.lift f (-g))))

end Quillen.CochainComplex
