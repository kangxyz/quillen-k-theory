/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.Functoriality
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Coherent G-theory as a genuine finite-pushforward functor

The covariant functor uses exactly the established coherent pushforward maps
on locally noetherian schemes and genuine finite morphisms. Its identity and
composition laws come from the actual geometric direct-image comparisons.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme

/-- Schemes with their genuine finite morphisms. -/
abbrev FiniteSchemes :=
  WideSubcategory (@AlgebraicGeometry.IsFinite : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance finiteSchemes_isFinite {X Y : FiniteSchemes.{u}}
    (f : X ⟶ Y) : AlgebraicGeometry.IsFinite f.hom := f.property

/-- Locally noetherian schemes among the genuine finite-morphism category. -/
abbrev locallyNoetherianFiniteSchemeProperty : ObjectProperty FiniteSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with actual finite morphisms as morphisms. -/
abbrev LocallyNoetherianFiniteSchemes := locallyNoetherianFiniteSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianFiniteSchemes_isLocallyNoetherian
    (X : LocallyNoetherianFiniteSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- Genuine covariant coherent G-theory on locally noetherian finite morphisms. -/
def GFinitePushforwardFunctor (n : ℕ) :
    LocallyNoetherianFiniteSchemes.{u} ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (AlgebraicGeometry.Scheme.Modules.Coherent.G X.obj.obj n)
  map f := GrpCat.ofHom
    (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap f.hom.hom
    n)
  map_id X := by
    apply GrpCat.hom_ext
    exact AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap_id
      X.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap_comp
      f.hom.hom g.hom.hom n

/-- The bundled map is precisely the established original pushforward homomorphism. -/
@[simp] theorem GFinitePushforwardFunctor_map {X Y : LocallyNoetherianFiniteSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ) : ((GFinitePushforwardFunctor n).map f).hom =
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.Finite.coherentPushforwardGMap f.hom.hom
        n := rfl

end AlgebraicGeometry.Scheme
