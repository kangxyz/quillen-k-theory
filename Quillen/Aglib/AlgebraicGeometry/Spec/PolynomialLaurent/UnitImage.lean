/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic

/-!
# Images of the original Laurent global unit

For an arbitrary ring morphism from a Laurent polynomial ring, the affine global-sections
isomorphism identifies the pulled-back original Laurent unit and its inverse with the literal
images of `T 1` and `T (-1)`. The proof uses naturality of `Scheme.ΓSpecIso`; no hypothesis
identifies a replacement scalar with the Laurent coordinate.
-/
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

/-- Pulling back the original Laurent unit gives the literal image of the coordinate. -/
lemma laurentGlobalUnit_image {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) :
    (Scheme.ΓSpecIso S).hom
        (↑(Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentGlobalUnit R))) =
      h.hom (LaurentPolynomial.T 1) := by
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality h)
    (↑(laurentGlobalUnit R))
  change (Scheme.ΓSpecIso S).hom ((Spec.map h).appTop (↑(laurentGlobalUnit R))) =
    h.hom ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      (↑(laurentGlobalUnit R))) at hn
  rw [laurentGlobalUnit_original_T] at hn
  exact hn

/-- The inverse of the pulled-back original Laurent unit is the literal inverse coordinate. -/
lemma laurentGlobalUnit_image_inv {R S : CommRingCat.{u}}
    (h : CommRingCat.of (LaurentPolynomial R) ⟶ S) :
    (Scheme.ΓSpecIso S).hom
        (↑((Units.map (Spec.map h).appTop.hom.toMonoidHom (laurentGlobalUnit R))⁻¹)) =
      h.hom (LaurentPolynomial.T (-1)) := by
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality h)
    (↑(laurentGlobalUnit R)⁻¹)
  change (Scheme.ΓSpecIso S).hom ((Spec.map h).appTop (↑(laurentGlobalUnit R)⁻¹)) =
    h.hom ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      (↑(laurentGlobalUnit R)⁻¹)) at hn
  have hi : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      (↑(laurentGlobalUnit R)⁻¹) = LaurentPolynomial.T (-1) := by
    change (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.T (-1))) = _
    exact ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv_hom_id _
  rw [hi] at hn
  exact hn

end AlgebraicGeometry.Scheme.PolynomialLaurent
