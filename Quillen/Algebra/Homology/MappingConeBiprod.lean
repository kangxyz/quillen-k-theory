/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Actual mapping cones and binary biproducts

The original chain mapping cone of a block-diagonal morphism is canonically
isomorphic to the binary biproduct of its original mapping cones. The maps
are the literal cone maps of the two projections and inclusions. The cone
inclusion commutes with this isomorphism. Only an additive category with
binary biproducts is required.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
open _root_.CochainComplex

lemma mappingCone_map_add {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) (a a' : K₁ ⟶ K₂) (b b' : L₁ ⟶ L₂)
    (h : f ≫ b = a ≫ g) (h' : f ≫ b' = a' ≫ g) :
    mappingCone.map f g (a + a') (b + b') (by simp [Preadditive.comp_add, Preadditive.add_comp, h,
      h']) =
      mappingCone.map f g a b h + mappingCone.map f g a' b' h' := by
  ext n
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map,
    Preadditive.comp_add, Preadditive.add_comp]

lemma mappingCone_map_zero {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    mappingCone.map f g 0 0 (by simp) = 0 := by
  ext n
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

/-- The mapping cone of a biproduct map is the biproduct of the two mapping cones. -/
def mappingConeBiprodIso {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    mappingCone (biprod.map f g) ≅ mappingCone f ⊞ mappingCone g where
  hom := biprod.lift
    (mappingCone.map (biprod.map f g) f biprod.fst biprod.fst (by simp))
    (mappingCone.map (biprod.map f g) g biprod.snd biprod.snd (by simp))
  inv := biprod.desc
    (mappingCone.map f (biprod.map f g) biprod.inl biprod.inl (by simp))
    (mappingCone.map g (biprod.map f g) biprod.inr biprod.inr (by simp))
  hom_inv_id := by
    rw [biprod.lift_desc, ← mappingCone.map_comp, ← mappingCone.map_comp,
      ← mappingCone_map_add]
    simp only [biprod.total, mappingCone.map_id]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp [← mappingCone.map_comp, mappingCone.map_id, mappingCone_map_zero]

@[reassoc]
lemma mappingConeBiprodIso_inr {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) :
    mappingCone.inr (biprod.map f g) ≫ (mappingConeBiprodIso f g).hom =
      biprod.map (mappingCone.inr f) (mappingCone.inr g) := by
  apply biprod.hom_ext <;>
    simp [mappingConeBiprodIso, mappingCone.map, Category.assoc]

end Quillen.CochainComplex
