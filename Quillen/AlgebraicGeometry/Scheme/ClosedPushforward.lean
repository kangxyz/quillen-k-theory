/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.PushforwardFunctoriality
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Coherent G-theory as a genuine closed-pushforward functor

The covariant functor uses exactly the established coherent pushforward maps
on locally noetherian schemes and genuine closed immersions. Its identity and
composition laws come from the actual geometric direct-image comparisons.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Scheme

/-- Schemes with their genuine closed-immersion morphisms. -/
abbrev ClosedImmersionSchemes :=
  WideSubcategory (@IsClosedImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance closedImmersionSchemes_isClosedImmersion {X Y : ClosedImmersionSchemes.{u}}
    (f : X ⟶ Y) : IsClosedImmersion f.hom := f.property

/-- Locally noetherian schemes among the genuine closed-immersion category. -/
abbrev locallyNoetherianClosedSchemeProperty : ObjectProperty ClosedImmersionSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with actual closed immersions as morphisms. -/
abbrev LocallyNoetherianClosedSchemes := locallyNoetherianClosedSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianClosedSchemes_isLocallyNoetherian
    (X : LocallyNoetherianClosedSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- Genuine covariant coherent G-theory on locally noetherian closed immersions. -/
def GClosedPushforwardFunctor (n : ℕ) : LocallyNoetherianClosedSchemes.{u} ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (CoherentScheme.G X.obj.obj n)
  map f := GrpCat.ofHom (CoherentScheme.ClosedImmersion.General.coherentPushforwardGMap f.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact CoherentScheme.ClosedImmersion.General.coherentPushforwardGMap_id X.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact CoherentScheme.ClosedImmersion.General.coherentPushforwardGMap_comp f.hom.hom g.hom.hom n

/-- The bundled map is precisely the established original pushforward homomorphism. -/
@[simp] theorem GClosedPushforwardFunctor_map {X Y : LocallyNoetherianClosedSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ) : ((GClosedPushforwardFunctor n).map f).hom =
      CoherentScheme.ClosedImmersion.General.coherentPushforwardGMap f.hom.hom n := rfl

end Quillen.Scheme
