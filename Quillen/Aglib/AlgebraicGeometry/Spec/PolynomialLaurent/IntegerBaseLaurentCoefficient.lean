/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseLaurentParameter

/-! # The complete integral Spec-row coefficient square

Candidate for Aglib: this retains the actual Laurent projection on the entire fixed-factor
product. Its consumer is the original parameter Laurent track under integral Spec restriction.

The intended upstream module is
`Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseLaurentCoefficient`.
The coefficient square assumes only a scheme over
`Spec (CommRingCat.of (ULift.{u} ℤ))` and a coefficient algebra under
`CommRingCat.of (ULift.{u} ℤ)`, retaining their original Laurent projection.
The current production consumer is
`Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientUnit`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow

/-- The whole Laurent comparison commutes with the original coefficient projection. -/
theorem laurentParameterIso_coefficient
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (laurentParameterIso Q a).hom ≫
        (baseProductFunctor (toIntegerBase Q.left)).map
          ((baseProductProjection (PolynomialLaurent.laurentProjection integerRing)).app
            (Spec a.right)) =
      laurentProjection Q a ≫ (canonicalRowIso Q a).hom := by
  simp only [laurentParameterIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp]
  dsimp only [baseProductProjection]
  rw [laurentSpecIso_hom_fst]
  exact (canonicalRowIso_coefficient Q ((laurentUnderCoefficient _).app a)).symm

end AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
