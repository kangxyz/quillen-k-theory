/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineRestrictionCoefficients
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.OpenLocalization

/-! # Sections of affine charts over an affine base

These comparisons preserve the original pushforward, restriction units, and
changes of the actual open arrow. No finiteness hypothesis is used.
-/

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.SchemeSheaf
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- The affine global-sections functor acts by the original map on top sections. -/
theorem globalSectionsMap_apply {M N : (Spec R).Modules} (f : M ⟶ N)
    (x : moduleSpecΓFunctor.obj M) :
    moduleSpecΓFunctor.map f x = f.app ⊤ x := rfl

/-- The affine pushforward comparison retains the original top section. -/
theorem pushforwardGlobalSectionsIso_hom_apply (N : (Spec S).Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N)) :
    (pushforwardGlobalSectionsIso φ).hom.app N x = x := rfl

end Quillen.SchemeSheaf
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf
variable {R A : CommRingCat.{u}} {X : Scheme.{u}}
variable (a : R ⟶ A) (j : Spec A ⟶ X) (p : X ⟶ Spec R) (h : j ≫ p = Spec.map a)

/-- Actual pushforward sections of an affine chart, with coefficients on the affine base. -/
def chartPushforwardSectionsIso :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.pushforward p ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars a.hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardComp j p) moduleSpecΓFunctor ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.pushforwardCongr h) moduleSpecΓFunctor ≪≫
    pushforwardGlobalSectionsIso a

/-- The chart pushforward comparison retains the original section. -/
theorem chartPushforwardSectionsIso_hom_apply (N : (Spec A).Modules)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward p).obj
      ((Scheme.Modules.pushforward j).obj N))) :
    (chartPushforwardSectionsIso a j p h).hom.app N x = x := by
  change N.presheaf.map (eqToHom (by simp)).op x = x
  simp

end Quillen.SchemeSheaf
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat Opposite
namespace Quillen.SchemeSheaf
variable {R A B : CommRingCat.{u}} {X : Scheme.{u}}
variable (a : R ⟶ A) (φ : A ⟶ B) (c : R ⟶ B) (hc : c.hom = φ.hom.comp a.hom)
variable (j : Spec A ⟶ X) (p : X ⟶ Spec R) (hj : j ≫ p = Spec.map a)
variable [IsOpenImmersion j] [IsOpenImmersion (Spec.map φ)]

include hc hj in
omit [IsOpenImmersion j] [IsOpenImmersion (Spec.map φ)] in
/-- A nested affine chart has the literal composite coefficient map. -/
theorem nestedProjection : (Spec.map φ ≫ j) ≫ p = Spec.map c := by
  rw [Category.assoc, hj, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact hc.symm

/-- The original localization map becomes the actual affine coefficient restriction map. -/
theorem original_nested_restriction (M : X.Modules) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward p).map
        (openLocalizationMap (Spec.map φ) j M)) ≫
      (chartPushforwardSectionsIso c (Spec.map φ ≫ j) p
        (nestedProjection a φ c hc j p hj)).hom.app (M.restrict (Spec.map φ ≫ j)) ≫
      (restrictScalars c.hom).map (moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictFunctorComp (Spec.map φ) j).hom.app M)) =
    (chartPushforwardSectionsIso a j p hj).hom.app (M.restrict j) ≫
      coefficientRestrictionMap a φ c hc (M.restrict j) := by
  apply ConcreteCategory.hom_ext
  intro x
  have hx := chartPushforwardSectionsIso_hom_apply a j p hj (M.restrict j) x
  have hy := chartPushforwardSectionsIso_hom_apply c (Spec.map φ ≫ j) p
    (nestedProjection a φ c hc j p hj) (M.restrict (Spec.map φ ≫ j))
    (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward p).map
      (openLocalizationMap (Spec.map φ) j M)) x)
  simp only [ModuleCat.comp_apply]
  erw [hx, hy]
  simp only [globalSectionsMap_apply, Scheme.Modules.pushforward_map_app,
    openLocalizationMap_app]
  erw [ModuleCat.restrictScalars.map_apply, globalSectionsMap_apply,
    Scheme.Modules.restrictFunctorComp_hom_app_app, coefficientRestrictionMap_apply,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  rw [Scheme.Modules.restrict_map]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl
end Quillen.SchemeSheaf
end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModuleCat
namespace Quillen.SchemeSheaf
variable {R A : CommRingCat.{u}} {X : Scheme.{u}} (a : R ⟶ A)
variable {j k : Spec A ⟶ X} [IsOpenImmersion j] [IsOpenImmersion k]
variable (p : X ⟶ Spec R) (h : j = k)
variable (hj : j ≫ p = Spec.map a) (hk : k ≫ p = Spec.map a)

/-- Changing equal chart arrows preserves the original localization comparison. -/
theorem chartPushforwardSections_congr (M : X.Modules) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward p).map
        ((openLocalizationCongr h).hom.app M)) ≫
      (chartPushforwardSectionsIso a k p hk).hom.app (M.restrict k) =
    (chartPushforwardSectionsIso a j p hj).hom.app (M.restrict j) ≫
      (restrictScalars a.hom).map (moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictFunctorCongr h).hom.app M)) := by
  subst k
  simp only [openLocalizationCongr, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  apply ConcreteCategory.hom_ext
  intro x
  simp only [ModuleCat.comp_apply]
  change _ = ((M.presheaf.map (eqToHom (by simp)).op)) _
  simp
end Quillen.SchemeSheaf
end

end
