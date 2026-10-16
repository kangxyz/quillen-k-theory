/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Relative

/-!
# Actual relative polynomial and Laurent coordinates

The genuine products over the integral terminal scheme carry their original positive open, second-projection coordinate, and forward Laurent unit on every base scheme.
-/
@[expose] public section


open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

open AlgebraicGeometry.Scheme.Products

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Bass

/-- The genuine relative affine line over an arbitrary scheme. -/
abbrev nativePolynomialScheme (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.{u} :=
  (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).obj X

/-- The genuine relative Laurent scheme over an arbitrary scheme. -/
abbrev nativeLaurentScheme (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.{u} :=
  (baseProductFunctor (PolynomialLaurent.laurentProjection integerRing)).obj X

/-- The original positive Laurent open, before imposing quasi-compactness on the base. -/
def nativeLaurentPlus (X : AlgebraicGeometry.Scheme.{u}) :
    nativeLaurentScheme X ⟶ nativePolynomialScheme X :=
  (baseProductTransformation _ _ (PolynomialLaurent.laurentPlus integerRing)
    (PolynomialLaurent.laurentPlus_projection integerRing)).app X

instance (X : AlgebraicGeometry.Scheme.{u}) : IsOpenImmersion (nativeLaurentPlus X) :=
  instIsOpenImmersionBaseProductTransformation _ _ _
    (PolynomialLaurent.laurentPlus_projection integerRing) X

/-- The polynomial coordinate pulled back along the actual second projection. -/
def nativePolynomialCoordinate (X : AlgebraicGeometry.Scheme.{u}) :
    Γ(nativePolynomialScheme X, ⊤) :=
  (pullback.snd (toIntegerBase X) (PolynomialLaurent.polynomialProjection integerRing)).appTop
    (PolynomialLaurent.polynomialGlobalCoordinate integerRing)

/-- The original forward T unit pulled back to the genuine relative Laurent scheme. -/
def nativeLaurentUnit (X : AlgebraicGeometry.Scheme.{u}) :
    (Γ(nativeLaurentScheme X, ⊤))ˣ :=
  Units.map
    ((pullback.snd (toIntegerBase X)
      (PolynomialLaurent.laurentProjection integerRing)).appTop.hom.toMonoidHom)
    (PolynomialLaurent.laurentGlobalUnit integerRing)

/-- The actual open map preserves the second projection and its forward coordinate. -/
theorem nativePolynomialCoordinate_laurentPlus (X : AlgebraicGeometry.Scheme.{u}) :
    (nativeLaurentPlus X).appTop (nativePolynomialCoordinate X) = ↑(nativeLaurentUnit X) := by
  let a := pullback.snd (toIntegerBase X) (PolynomialLaurent.polynomialProjection integerRing)
  let b := pullback.snd (toIntegerBase X) (PolynomialLaurent.laurentProjection integerRing)
  have h : nativeLaurentPlus X ≫ a = b ≫ PolynomialLaurent.laurentPlus integerRing := by
    simp [nativeLaurentPlus, baseProductTransformation, a, b]
  have hc := congrArg (fun f ↦ f.appTop) h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at hc
  have he := ConcreteCategory.congr_hom hc
    (PolynomialLaurent.polynomialGlobalCoordinate integerRing)
  change (nativeLaurentPlus X).appTop
      (a.appTop (PolynomialLaurent.polynomialGlobalCoordinate integerRing)) =
    b.appTop ((PolynomialLaurent.laurentPlus integerRing).appTop
      (PolynomialLaurent.polynomialGlobalCoordinate integerRing)) at he
  rw [PolynomialLaurent.polynomialGlobalCoordinate_laurentPlus] at he
  exact he

/-- On quasi-compact bases this is literally the preexisting native Bass plus map. -/
theorem nativeLaurentPlus_eq_plus (X : QuasiCompactSchemes.{u}) :
    nativeLaurentPlus X.obj = (plus.app X).hom := rfl

end AlgebraicGeometry.Scheme.Bass


end

end
