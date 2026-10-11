/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Category.ModuleCat.Sheaf.Tensor

/-!
# Consumers of the actual sheafified tensor

These statements inspect both original tensor maps, their interchange and composition,
and the original presheaf-unitor/sheafification-counit comparison.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.MonoidalCategory SheafOfModulesOfCommRing

namespace Quillen.Tests.SheafTensor

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The two literal presheaf tensor maps commute after original sheafification. -/
theorem original_tensor_square {M N P Q : SheafOfModulesOfCommRing R}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (associatedSheaf R).map (𝟙 ((toPresheaf R).obj M) ⊗ₘ (toPresheaf R).map g) ≫
      (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ 𝟙 ((toPresheaf R).obj Q)) =
    (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ 𝟙 ((toPresheaf R).obj P)) ≫
      (associatedSheaf R).map (𝟙 ((toPresheaf R).obj N) ⊗ₘ (toPresheaf R).map g) :=
  tensorFunctor_naturality R f g

/-- First-variable composition uses the original composed sheaf arrow. -/
theorem original_first_composition {M N P : SheafOfModulesOfCommRing R}
    (f : M ⟶ N) (g : N ⟶ P) (Q : SheafOfModulesOfCommRing R) :
    (associatedSheaf R).map ((toPresheaf R).map (f ≫ g) ⊗ₘ
      𝟙 ((toPresheaf R).obj Q)) =
    (associatedSheaf R).map ((toPresheaf R).map f ⊗ₘ 𝟙 ((toPresheaf R).obj Q)) ≫
      (associatedSheaf R).map ((toPresheaf R).map g ⊗ₘ 𝟙 ((toPresheaf R).obj Q)) :=
  congrArg (fun α => α.app Q) ((tensorFunctor R).map_comp f g)

/-- Second-variable composition uses the original composed sheaf arrow. -/
theorem original_second_composition (M : SheafOfModulesOfCommRing R)
    {N P Q : SheafOfModulesOfCommRing R} (f : N ⟶ P) (g : P ⟶ Q) :
    (associatedSheaf R).map (𝟙 ((toPresheaf R).obj M) ⊗ₘ
      (toPresheaf R).map (f ≫ g)) =
    (associatedSheaf R).map (𝟙 ((toPresheaf R).obj M) ⊗ₘ (toPresheaf R).map f) ≫
      (associatedSheaf R).map (𝟙 ((toPresheaf R).obj M) ⊗ₘ (toPresheaf R).map g) :=
  (tensorLeftFunctor R M).map_comp f g

/-- The unit comparison identifies the tensor of an actual sheaf arrow with that arrow. -/
theorem original_unit_map {M N : SheafOfModulesOfCommRing R} (f : M ⟶ N) :
    (tensorLeftUnitIso R).inv.app M ≫
      (tensorLeftFunctor R (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).map f ≫
      (tensorLeftUnitIso R).hom.app N = f := by
  rw [← Category.assoc, ← (tensorLeftUnitIso R).inv.naturality f]
  simp

/-- The original unitor followed by the actual counit has the stated inverse. -/
theorem original_counit_unitor_inverse (M : SheafOfModulesOfCommRing R) :
    ((associatedSheaf R).map (λ_ ((toPresheaf R).obj M)).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (𝟙 _)).counit.app M) ≫
    (inv ((PresheafOfModules.sheafificationAdjunction
        (R := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (𝟙 _)).counit.app M) ≫
      (associatedSheaf R).map (λ_ ((toPresheaf R).obj M)).inv) = 𝟙 _ := by
  rw [← tensorLeftUnitIso_hom_app, ← tensorLeftUnitIso_inv_app]
  exact (tensorLeftUnitIso R).hom_inv_id_app M

end Quillen.Tests.SheafTensor
