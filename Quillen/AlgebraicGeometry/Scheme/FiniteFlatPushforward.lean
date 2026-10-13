/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.FinitePushforwardFunctoriality
public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.AlgebraicGeometry.Scheme.FinitePushforward

/-! # Covariant vector-bundle K-theory for finite flat morphisms

The public functor uses the original finite flat vector-bundle direct image.
Forgetting flatness retains the original scheme and its finite morphism.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Scheme

/-- Actual finite flat scheme morphisms. -/
abbrev finiteFlatMorphisms : MorphismProperty AlgebraicGeometry.Scheme.{u} :=
  (@AlgebraicGeometry.IsFinite) ⊓ (@Flat)

instance finiteFlatMorphisms_isMultiplicative : finiteFlatMorphisms.{u}.IsMultiplicative :=
  inferInstanceAs ((@AlgebraicGeometry.IsFinite ⊓ @Flat :
    MorphismProperty AlgebraicGeometry.Scheme.{u}).IsMultiplicative)

/-- Schemes with finite flat morphisms. -/
abbrev FiniteFlatSchemes := WideSubcategory finiteFlatMorphisms.{u}

instance finiteFlatSchemes_isFinite {X Y : FiniteFlatSchemes.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.IsFinite f.hom := f.property.1

instance finiteFlatSchemes_flat {X Y : FiniteFlatSchemes.{u}} (f : X ⟶ Y) :
    Flat f.hom := f.property.2

/-- Locally noetherian objects in the finite flat scheme category. -/
abbrev locallyNoetherianFiniteFlatSchemeProperty : ObjectProperty FiniteFlatSchemes.{u} :=
  fun X ↦ IsLocallyNoetherian X.obj

/-- Locally noetherian schemes and actual finite flat morphisms. -/
abbrev LocallyNoetherianFiniteFlatSchemes :=
  locallyNoetherianFiniteFlatSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianFiniteFlatSchemes_isLocallyNoetherian
    (X : LocallyNoetherianFiniteFlatSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- Genuine covariant vector-bundle K-theory for finite flat direct image. -/
def KFiniteFlatPushforwardFunctor (n : ℕ) :
    LocallyNoetherianFiniteFlatSchemes.{u} ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.obj.obj n)
  map f := GrpCat.ofHom (SchemeSheaf.schemeKPushforward f.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact SchemeSheaf.schemeKPushforward_id X.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact SchemeSheaf.schemeKPushforward_comp f.hom.hom g.hom.hom n

/-- Forgetting flatness retains the original schemes and finite scheme maps. -/
def forgetFiniteFlat : LocallyNoetherianFiniteFlatSchemes.{u} ⥤ LocallyNoetherianFiniteSchemes.{u}
    where
  obj X := ⟨⟨X.obj.obj⟩, X.property⟩
  map f := ObjectProperty.homMk ⟨f.hom.hom, f.hom.property.1⟩

end Quillen.Scheme
