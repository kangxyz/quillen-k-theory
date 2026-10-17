/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Original cocartesian lifts in the covariant Grothendieck construction

The original pseudofunctor image supplies the lift object. The identity in that fiber supplies
the lift arrow. Its strong cocartesian universal property uses the actual composition comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckCocartesian
variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}}
  {R S : C} (x : F.obj ⟨R⟩) (f : R ⟶ S)

/-- The target is the actual image under the original pseudofunctor. -/
abbrev target : Pseudofunctor.Grothendieck F := ⟨S, (F.map f.toLoc).toFunctor.obj x⟩

/-- The original identity-fiber cocartesian lift. -/
abbrev lift : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ target x f := ⟨f, 𝟙 _⟩

instance instIsHomLift : (Pseudofunctor.Grothendieck.forget F).IsHomLift f (lift x f) :=
  IsHomLift.map _ (lift x f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The factorization through the lift uses the original inverse composition comparison. -/
abbrev factor {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] : target x f ⟶ z where
  base := g
  fiber :=
    have h : φ.base = f ≫ g := by
      simpa using IsHomLift.fac' (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ
    (F.mapComp f.toLoc g.toLoc).inv.toNatTrans.app x ≫ eqToHom (by simp [h]) ≫ φ.fiber

instance instIsHomLiftFactor {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] :
    (Pseudofunctor.Grothendieck.forget F).IsHomLift g (factor x f g φ) :=
  IsHomLift.map _ (factor x f g φ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original factorization composes with the original lift to the supplied arrow. -/
theorem factor_fac {z : Pseudofunctor.Grothendieck F} (g : S ⟶ z.base)
    (φ : (⟨R, x⟩ : Pseudofunctor.Grothendieck F) ⟶ z)
    [(Pseudofunctor.Grothendieck.forget F).IsHomLift (f ≫ g) φ] :
    lift x f ≫ factor x f g φ = φ :=
  Pseudofunctor.Grothendieck.Hom.ext _ _
    (by simpa using IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ)
    (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every original identity-fiber lift is genuinely strongly cocartesian. -/
instance instIsStronglyCocartesian :
    (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f (lift x f) where
  universal_property' {z} g φ hφ := by
    refine ⟨factor x f g φ, ⟨inferInstance, ?_⟩, ?_⟩
    · exact Pseudofunctor.Grothendieck.Hom.ext _ _
        (by simpa using IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ)
        (by simp)
    rintro χ ⟨hχ, rfl⟩
    obtain ⟨rfl⟩ : g = χ.base := by
      simpa using IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) g χ
    ext <;> simp

end Quillen.CategoryTheory.GrothendieckCocartesian
