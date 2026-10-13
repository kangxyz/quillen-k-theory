/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.MatrixDeflation

/-! # Admissible monomorphisms with an extra matrix entry

The actual biproduct map with an admissible first coordinate is admissible.
The proof uses only exact-category axioms and explicit universal properties.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Adding an unchanged summand is a genuine cobase change. -/
theorem isPushout_biprod_map_left {A B D : C} (i : A ⟶ B) :
    IsPushout (biprod.inl : A ⟶ A ⊞ D) i
      (biprod.map i (𝟙 D)) (biprod.inl : B ⟶ B ⊞ D) := by
  apply IsPushout.mk' (by simp)
  · intro W φ ψ h₁ h₂
    apply biprod.hom_ext' _ _ h₂
    simpa using congrArg (fun k ↦ biprod.inr ≫ k) h₁
  · intro W a b h
    refine ⟨biprod.desc b (biprod.inr ≫ a), ?_, by simp⟩
    apply biprod.hom_ext'
    · simpa using h.symm
    · simp

/-- The graph of an arbitrary morphism is an admissible monomorphism. -/
theorem inflation_graph (E : Quillen.ExactStructure C) {A D : C} (f : A ⟶ D) :
    E.inflation (biprod.lift (𝟙 A) f) := by
  let p := biprod.desc (-f) (𝟙 D)
  have hp : E.deflation p := E.deflation_biprod_desc (-f) (𝟙 D) (E.deflation_id D)
  apply E.inflation_of_isKernel (p := p) (by simp [p]) _ hp
  refine KernelFork.IsLimit.ofι _ _ (fun g _ ↦ g ≫ biprod.fst) ?_ ?_
  · intro W g hg
    apply biprod.hom_ext
    · simp
    · have hh : -(g ≫ biprod.fst ≫ f) + g ≫ biprod.snd = 0 := by
        simpa [p, biprod.desc_eq, Category.assoc] using hg
      simpa using (neg_add_eq_zero.mp hh)
  · intro W g hg m hm
    simpa using congrArg (fun k ↦ k ≫ biprod.fst) hm

/-- Adding an arbitrary second coordinate to an admissible mono keeps it admissible. -/
theorem inflation_biprod_lift (E : Quillen.ExactStructure C) {A B D : C}
    (i : A ⟶ B) (f : A ⟶ D) (hi : E.inflation i) :
    E.inflation (biprod.lift i f) := by
  have hm : E.inflation (biprod.map i (𝟙 D)) :=
    E.inflation.of_isPushout (isPushout_biprod_map_left i) hi
  have hc := E.inflation_comp _ _ (E.inflation_graph f) hm
  convert hc using 1
  ext <;> simp

end Quillen.ExactStructure
