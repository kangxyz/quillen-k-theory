/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeProductTransport

/-!
# The original common corner under independent Bass contraction

The actual polynomial/Laurent product swap preserves the original coefficient projection.
Consequently contraction of the original polynomial coefficient map is the same coefficient
map on the contracted row, under the original product transport. The proof uses the actual
Laurent quotient and its naturality; it makes no assertion identifying a transported boundary
with the canonical quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart

/-- The original coefficient projection commutes with the literal Laurent factor swap. -/
@[reassoc]
theorem productLaurentOppositeIso_polynomialProjection
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (NatTrans.op polynomialProjection).app (laurentFunctor.op.obj X) ≫
        (productLaurentOppositeIso (PolynomialLaurent.polynomialProjection integerRing)).hom.app X =
      laurentFunctor.op.map ((NatTrans.op polynomialProjection).app X) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact qcBaseProductSwapIso_projection_first
    (PolynomialLaurent.polynomialProjection integerRing)
    (PolynomialLaurent.laurentProjection integerRing) X.unop

/-- Product transport retains the actual common-corner coefficient map after contraction. -/
@[reassoc]
theorem productContractionTransportIso_polynomialProjection
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op plus) (NatTrans.op minus)
      (Functor.whiskerRight (NatTrans.op polynomialProjection) F)).app X ≫
        (productContractionTransportIso
          (PolynomialLaurent.polynomialProjection integerRing) F).hom.app X =
      (contraction (NatTrans.op plus) (NatTrans.op minus) F).map
        ((NatTrans.op polynomialProjection).app X) := by
  apply (cancel_epi ((contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app X)).mp
  rw [← Category.assoc, contractionMap_π, Category.assoc]
  have hp := productContractionTransportIso_π
    (PolynomialLaurent.polynomialProjection integerRing) F X
  change (contractionπ (NatTrans.op plus) (NatTrans.op minus)
      (polynomialFunctor.op ⋙ F)).app X ≫
        (productContractionTransportIso
          (PolynomialLaurent.polynomialProjection integerRing) F).hom.app X =
      F.map ((productLaurentOppositeIso
        (PolynomialLaurent.polynomialProjection integerRing)).hom.app X) ≫
          (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
            (polynomialFunctor.op.obj X) at hp
  rw [hp]
  calc
    _ = (F.map ((NatTrans.op polynomialProjection).app (laurentFunctor.op.obj X)) ≫
        F.map ((productLaurentOppositeIso
          (PolynomialLaurent.polynomialProjection integerRing)).hom.app X)) ≫
        (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
          (polynomialFunctor.op.obj X) := (Category.assoc _ _ _).symm
    _ = F.map ((NatTrans.op polynomialProjection).app (laurentFunctor.op.obj X) ≫
        (productLaurentOppositeIso
          (PolynomialLaurent.polynomialProjection integerRing)).hom.app X) ≫
        (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
          (polynomialFunctor.op.obj X) :=
      congrArg (fun g => g ≫ (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
        (polynomialFunctor.op.obj X)) (F.map_comp _ _).symm
    _ = F.map (laurentFunctor.op.map ((NatTrans.op polynomialProjection).app X)) ≫
        (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
          (polynomialFunctor.op.obj X) :=
      congrArg (fun g => F.map g ≫ (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
        (polynomialFunctor.op.obj X)) (productLaurentOppositeIso_polynomialProjection X)
    _ = _ := (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).naturality
      ((NatTrans.op polynomialProjection).app X)


end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
