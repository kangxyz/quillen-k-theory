/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Category

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.PushforwardFunctoriality
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Coherent G-theory as a genuine closed-pushforward functor

The covariant functor uses exactly the established coherent pushforward maps
on locally noetherian schemes and genuine closed immersions. Its identity and
composition laws come from the actual geometric direct-image comparisons.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme

/-- Genuine covariant coherent G-theory on locally noetherian closed immersions. -/
def GClosedPushforwardFunctor (n : ℕ) : LocallyNoetherianClosedSchemes.{u} ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (AlgebraicGeometry.Scheme.Modules.Coherent.G X.obj.obj n)
  map f := GrpCat.ofHom
    (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap
    f.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact
AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap_id
      X.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap_comp f.hom.hom
      g.hom.hom n

/-- The bundled map is precisely the established original pushforward homomorphism. -/
@[simp] theorem GClosedPushforwardFunctor_map {X Y : LocallyNoetherianClosedSchemes.{u}}
    (f : X ⟶ Y) (n : ℕ) : ((GClosedPushforwardFunctor n).map f).hom =
      AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap
        f.hom.hom n := rfl

end AlgebraicGeometry.Scheme
