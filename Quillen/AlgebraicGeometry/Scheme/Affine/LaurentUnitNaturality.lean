/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Affine.PolynomialLaurent
public import Quillen.Algebra.Polynomial.LaurentBaseChange

/-! The actual Laurent global unit is preserved by every coefficient morphism. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange
universe u
namespace Quillen.Scheme.PolynomialLaurent

/-- Coefficient pullback preserves the original Laurent coordinate as a genuine global unit. -/
lemma laurentGlobalUnit_coefficient {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Units.map (Spec.map (laurentMap f)).appTop.hom.toMonoidHom (laurentGlobalUnit R) =
      laurentGlobalUnit S := by
  apply Units.ext
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial S))).hom).injective
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial S))).hom
    ((Spec.map (laurentMap f)).appTop (↑(laurentGlobalUnit R))) = _
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (laurentMap f))
    (↑(laurentGlobalUnit R))
  change (Scheme.ΓSpecIso (.of (LaurentPolynomial S))).hom
    ((Spec.map (laurentMap f)).appTop (↑(laurentGlobalUnit R))) =
      laurentMap f ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom
        (↑(laurentGlobalUnit R))) at h
  rw [laurentGlobalUnit_original_T, laurentMap_T] at h
  rw [laurentGlobalUnit_original_T]
  exact h

end Quillen.Scheme.PolynomialLaurent
