/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent

/-!
# The original polynomial coordinate on the Laurent open

The actual polynomial global section X restricts to the existing Laurent global unit T.
No invertibility of X on the whole polynomial spectrum is asserted.
-/
@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The literal polynomial variable as an original global section of the polynomial spectrum. -/
def polynomialGlobalCoordinate (R : CommRingCat.{u}) : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv (Polynomial.X : Polynomial R)

/-- Original affine global sections identify this coordinate with the unchanged polynomial X. -/
theorem polynomialGlobalCoordinate_original (R : CommRingCat.{u}) :
    (Scheme.ΓSpecIso (.of (Polynomial R))).hom (polynomialGlobalCoordinate R) =
      (Polynomial.X : Polynomial R) := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of (Polynomial R))).inv_hom_id _

/-- On the original positive Laurent open, X is exactly the existing Laurent global unit T. -/
theorem polynomialGlobalCoordinate_laurentPlus (R : CommRingCat.{u}) :
    (laurentPlus R).appTop (polynomialGlobalCoordinate R) = ↑(laurentGlobalUnit R) := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).injective
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Polynomial.toLaurent (R := R))))
    (polynomialGlobalCoordinate R)
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
    ((laurentPlus R).appTop (polynomialGlobalCoordinate R)) =
      Polynomial.toLaurent ((Scheme.ΓSpecIso (.of (Polynomial R))).hom
        (polynomialGlobalCoordinate R)) at h
  rw [polynomialGlobalCoordinate_original, Polynomial.toLaurent_X] at h
  rw [laurentGlobalUnit_original_T]
  exact h

end AlgebraicGeometry.Scheme.PolynomialLaurent
