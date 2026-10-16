/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckCocartesian
public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckFiber

/-!
# Original fiber components of cocartesian arrows are invertible

The original identity-fiber lift factors a supplied cocartesian arrow through its actual fiber
component. Cocartesian cancellation and the identity base prove this component invertible.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckCocartesian
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

private theorem isIso_fiberHom {E : Type*} [Category* E] {π : E ⥤ C} {R : C}
    {a b : Functor.Fiber π R} (f : a ⟶ b) [IsIso f.val] : IsIso f := by
  have : π.IsHomLift (𝟙 R) f.val := f.property
  refine ⟨⟨⟨inv f.val, inferInstance⟩, ?_, ?_⟩⟩
  · apply Subtype.ext
    exact IsIso.hom_inv_id f.val
  · apply Subtype.ext
    exact IsIso.inv_hom_id f.val

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The supplied original arrow factors through the original lift and its actual fiber map. -/
theorem lift_fiber {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b) :
    lift a.fiber φ.base ≫ (GrothendieckFiber.inclusion F b.base).map φ.fiber = φ := by
  refine Pseudofunctor.Grothendieck.Hom.ext _ _ (by simp [GrothendieckFiber.inclusion]) ?_
  simp [GrothendieckFiber.inclusion, F.mapComp_id_right_hom_app,
    Strict.rightUnitor_eqToIso]

/-- Strong cocartesianness makes the original fiber component an actual isomorphism. -/
theorem isIso_fiber {a b : Pseudofunctor.Grothendieck F} (φ : a ⟶ b)
    [(Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian φ.base φ] :
    IsIso φ.fiber := by
  let ψ := (GrothendieckFiber.toFiber F b.base).map φ.fiber
  have hψ : (Pseudofunctor.Grothendieck.forget F).IsHomLift (𝟙 b.base) ψ.val := ψ.property
  have hcomp : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (φ.base ≫ 𝟙 b.base) (lift a.fiber φ.base ≫ ψ.val) := by
    change (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian
      (φ.base ≫ 𝟙 b.base)
      (lift a.fiber φ.base ≫ (GrothendieckFiber.inclusion F b.base).map φ.fiber)
    rw [lift_fiber, Category.comp_id]
    infer_instance
  have : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian (𝟙 b.base) ψ.val :=
    Functor.IsStronglyCocartesian.of_comp (Pseudofunctor.Grothendieck.forget F)
      (f := φ.base) (φ := lift a.fiber φ.base)
  have : IsIso ψ.val := Functor.IsStronglyCocartesian.isIso_of_base_isIso
    (Pseudofunctor.Grothendieck.forget F) (𝟙 b.base) ψ.val
  have : IsIso ψ := isIso_fiberHom ψ
  exact isIso_of_reflects_iso φ.fiber (GrothendieckFiber.toFiber F b.base)

end Quillen.CategoryTheory.GrothendieckCocartesian
