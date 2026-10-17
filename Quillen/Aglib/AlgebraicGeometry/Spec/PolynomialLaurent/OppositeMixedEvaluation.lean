/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.LaurentHyperbola

/-!
# Opposite Laurent evaluation and its actual spectrum coordinates

Laurent inversion gives the original opposite mixed ring map, its surjectivity,
signed kernel equation, and literal two spectrum projection formulas.
-/
@[expose] public section

open Quillen.PolynomialBaseChange


open CommRingCat.PolynomialLaurent

open Quillen


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent Quillen.PolynomialDiagonal
/-- The original opposite mixed evaluation sends the first variable to T^-1 and the second to T. -/
def oppositeMixedEvaluation (R : CommRingCat.{u}) :
    CommRingCat.of (Polynomial (Polynomial R)) ⟶ CommRingCat.of (LaurentPolynomial R) :=
  CommRingCat.ofHom (LaurentPolynomial.invert.toRingHom.comp (mixedEvaluation R))
/-- Inversion of the actual Laurent ring preserves surjectivity of its original evaluation. -/
theorem oppositeMixedEvaluation_surjective (R : CommRingCat.{u}) :
    Function.Surjective (oppositeMixedEvaluation R).hom :=
  LaurentPolynomial.invert.surjective.comp (mixedEvaluation_surjective R)
/-- The opposite mixed kernel retains the signed incidence equation 1 - t*u. -/
theorem oppositeMixedEvaluation_ker (R : CommRingCat.{u}) :
    RingHom.ker (oppositeMixedEvaluation R).hom =
      Ideal.span {1 - C (X : Polynomial R) * X} := by
  change RingHom.ker (LaurentPolynomial.invert.toRingHom.comp (mixedEvaluation R)) = _
  rw [RingHom.ker_comp_of_injective _ LaurentPolynomial.invert.injective,
    mixedEvaluation_ker]
  rw [← neg_sub, Ideal.span_singleton_neg]
/-- The first opposite coordinate is the original negative overlap leg. -/
theorem oppositeMixedEvaluation_first (R : CommRingCat.{u}) :
    Spec.map (oppositeMixedEvaluation R) ≫ (polynomialSquareIso R).hom ≫
      polynomialFirst R = laurentMinus R := by
  rw [polynomialSquareIso_hom_first]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom Polynomial.C) = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simp [oppositeMixedEvaluation, mixedEvaluation]
/-- The second coordinate is the original positive Laurent overlap leg. -/
theorem oppositeMixedEvaluation_second (R : CommRingCat.{u}) :
    Spec.map (oppositeMixedEvaluation R) ≫ (polynomialSquareIso R).hom ≫
      polynomialSecond R = laurentPlus R := by
  rw [polynomialSquareIso_hom_second]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext r <;> simp [oppositeMixedEvaluation, mixedEvaluation, polynomialMap]
end AlgebraicGeometry.Scheme.ProjectiveLine
