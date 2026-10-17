/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.Algebra.Polynomial.Laurent.Diagonal
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.AffineDiagonal

/-!
# Actual Laurent hyperbola in the polynomial affine plane

The original mixed evaluation map induces the two actual Laurent coordinate
maps into the affine plane. Its surjectivity proves the induced map is a closed
immersion. Actual projective-line chart assembly is kept downstream.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialDiagonal
/-- The original mixed affine diagonal induced by T and its inverse. -/
def mixedPolynomialDiagonal (R : CommRingCat.{u}) :
    Spec (.of (LaurentPolynomial R)) ⟶ polynomialSquare R :=
  Spec.map (CommRingCat.ofHom (mixedEvaluation R)) ≫ (polynomialSquareIso R).hom
@[reassoc (attr := simp)]
theorem mixedPolynomialDiagonal_first (R : CommRingCat.{u}) :
    mixedPolynomialDiagonal R ≫ polynomialFirst R = laurentPlus R := by
  rw [mixedPolynomialDiagonal, Category.assoc, polynomialSquareIso_hom_first]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simp [mixedEvaluation]
@[reassoc (attr := simp)]
theorem mixedPolynomialDiagonal_second (R : CommRingCat.{u}) :
    mixedPolynomialDiagonal R ≫ polynomialSecond R = laurentMinus R := by
  rw [mixedPolynomialDiagonal, Category.assoc, polynomialSquareIso_hom_second]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [mixedEvaluation, polynomialMap]
/-- The mixed diagonal is a closed immersion because its original ring map is surjective. -/
instance (R : CommRingCat.{u}) : IsClosedImmersion (mixedPolynomialDiagonal R) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (mixedEvaluation R))) :=
    IsClosedImmersion.spec_of_surjective _ (mixedEvaluation_surjective R)
  exact inferInstanceAs (IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (mixedEvaluation R)) ≫ (polynomialSquareIso R).hom))
end AlgebraicGeometry.Scheme.ProjectiveLine
