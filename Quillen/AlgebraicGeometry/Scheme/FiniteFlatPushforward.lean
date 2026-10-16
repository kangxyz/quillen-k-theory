/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Category

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.FinitePushforwardFunctoriality
public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.AlgebraicGeometry.Scheme.FinitePushforward

/-! # Covariant vector-bundle K-theory for finite flat morphisms

The public functor uses the original finite flat vector-bundle direct image.
Forgetting flatness retains the original scheme and its finite morphism.
-/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Genuine covariant vector-bundle K-theory for finite flat direct image. -/
def KFiniteFlatPushforwardFunctor (n : ℕ) :
    LocallyNoetherianFiniteFlatSchemes.{u} ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (K X.obj.obj n)
  map f := GrpCat.ofHom (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f.hom.hom n)
  map_id X := by
    apply GrpCat.hom_ext
    exact AlgebraicGeometry.Scheme.Modules.schemeKPushforward_id X.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact AlgebraicGeometry.Scheme.Modules.schemeKPushforward_comp f.hom.hom g.hom.hom n

end AlgebraicGeometry.Scheme
