/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates

/-! # Original polynomial coordinate and its actual Laurent restriction formulas -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})

/-- The original polynomial coordinate section under the canonical affine section isomorphism. -/
def polynomialCoordinate : Γ(Spec (.of (Polynomial R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom Polynomial.X

lemma laurentPlus_coordinate :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((laurentPlus R).appTop.hom (polynomialCoordinate R)) = LaurentPolynomial.T 1 := by
  have h := congrArg (fun f => CommRingCat.Hom.hom f (polynomialCoordinate R))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simpa [laurentPlus, polynomialCoordinate] using h

lemma laurentMinus_coordinate :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((laurentMinus R).appTop.hom (polynomialCoordinate R)) = LaurentPolynomial.T (-1) := by
  have h := congrArg (fun f => CommRingCat.Hom.hom f (polynomialCoordinate R))
    (Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent :
        Polynomial R →+* LaurentPolynomial R)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  simpa [laurentMinus, polynomialCoordinate] using h

end AlgebraicGeometry.Scheme.ProjectiveLine
