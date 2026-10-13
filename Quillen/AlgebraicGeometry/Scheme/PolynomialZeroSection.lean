/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.PolynomialLaurent

/-!
# Zero sections of the original polynomial products

Polynomial evaluation at zero supplies a section of the original affine-line
projection. Base change over the same integral terminal scheme gives a natural
section of the existing polynomial functor, without replacing its pullbacks.
The projection triangle is an equality of the original morphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Quillen.Scheme.PolynomialLaurent

/-- The actual affine zero section induced by polynomial evaluation at zero. -/
def polynomialZero (R : CommRingCat.{u}) : Spec R ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))

@[reassoc (attr := simp)]
theorem polynomialZero_projection (R : CommRingCat.{u}) :
    polynomialZero R ≫ polynomialProjection R = 𝟙 (Spec R) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 R := by
    apply CommRingCat.hom_ext
    ext r
    change Polynomial.eval 0 (Polynomial.C r) = r
    simp
  rw [h, Spec.map_id]

end Quillen.Scheme.PolynomialLaurent

namespace Quillen.Scheme.Bass

/-- Zero evaluation on the same native polynomial product over an arbitrary scheme. -/
def nativePolynomialZero (X : AlgebraicGeometry.Scheme.{u}) :
    X ⟶ (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).obj X :=
  pullback.lift (𝟙 X) (toIntegerBase X ≫ PolynomialLaurent.polynomialZero integerRing)
    (by simp)

@[reassoc (attr := simp)]
theorem nativePolynomialZero_projection (X : AlgebraicGeometry.Scheme.{u}) :
    nativePolynomialZero X ≫
      (baseProductProjection (PolynomialLaurent.polynomialProjection integerRing)).app X =
      𝟙 X := by
  simp [nativePolynomialZero, baseProductProjection]

@[reassoc]
theorem nativePolynomialZero_naturality {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    f ≫ nativePolynomialZero Y = nativePolynomialZero X ≫
      (baseProductFunctor (PolynomialLaurent.polynomialProjection integerRing)).map f := by
  apply pullback.hom_ext <;> simp [nativePolynomialZero, baseProductFunctor]

/-- The natural zero section of the original endofunctor on quasi-compact schemes. -/
def polynomialZero : 𝟭 QuasiCompactSchemes.{u} ⟶ polynomialFunctor where
  app X := ⟨nativePolynomialZero X.obj⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    exact nativePolynomialZero_naturality f.hom

@[reassoc (attr := simp)]
theorem polynomialZero_projection (X : QuasiCompactSchemes.{u}) :
    polynomialZero.app X ≫ polynomialProjection.app X = 𝟙 X := by
  apply ObjectProperty.hom_ext
  exact nativePolynomialZero_projection X.obj

/-- The original projection has the same zero section at the functor level. -/
theorem polynomialZero_comp_projection : polynomialZero ≫ polynomialProjection = 𝟙 _ := by
  ext X
  exact congrArg (fun f => f.hom) (polynomialZero_projection X)

end Quillen.Scheme.Bass
