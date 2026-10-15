/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Quillen.AlgebraicGeometry.Scheme.PolynomialLaurent

/-! The actual relative Laurent-unit K-one comparison over every base scheme.
Both schemes are the original products over the integral terminal scheme. The coordinate
and unit come from their second projections; no affine replacement of the base is used. -/

@[expose] public section
open Quillen

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

namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Bass

/-- Every perfect object over the true relative affine line has the original unit comparison. -/
theorem nativeScalarForwardKOneClass_restrict (X : Scheme.{u})
    (K : Perfect (nativePolynomialScheme X)) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarForwardKOneClass (nativeLaurentPlus X) K
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        ((perfectRestrict (nativeLaurentPlus X)).obj K) :=
  perfectScalarForwardKOneClass_restrict _ _ _ _ _

/-- The normalized forward square restricts to [T] on the genuine rank-one structure sheaf. -/
theorem nativeScalarForwardKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarForwardKOneClass (nativeLaurentPlus X)
          (rankOnePerfect (nativePolynomialScheme X))
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        (rankOnePerfect (nativeLaurentScheme X)) :=
  perfectScalarForwardKOneClass_restrict_rankOne _ _ _ _

/-- The cofiber boundary keeps its accepted inverse orientation on every relative Laurent open. -/
theorem nativeScalarCofiberBoundaryKOneClass_restrict_rankOne (X : Scheme.{u}) :
    perfectOpenKRestrict (nativeLaurentPlus X) 1
        (perfectScalarCofiberBoundaryKOneClass (nativeLaurentPlus X)
          (rankOnePerfect (nativePolynomialScheme X))
          (nativePolynomialCoordinate X) (nativeLaurentUnit X)
          (nativePolynomialCoordinate_laurentPlus X)) =
      (perfectGlobalUnitKOneClass (nativeLaurentScheme X) (nativeLaurentUnit X)
        (rankOnePerfect (nativeLaurentScheme X)))⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_restrict_rankOne _ _ _ _

end Quillen.PerfectComplexes
