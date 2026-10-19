/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeDoubleForwardQuotient
public import Quillen.KTheory.Bass.SchemeContractionBlockSwap
public import Quillen.KTheory.Bass.TwoChartMapIso

/-!
# The actual double-quotient swap on original bounded-flat K-zero

The native twice-positive comparison is natural on all quasi-compact schemes,
but invertibility is used only at the four actual polynomial/Laurent charts
of a fixed quasi-separated scheme. The genuine four-variable block conjugacy
moves the proved K-two sign into the required pair of variables. Naturality
then determines the swap on the original fixed K-zero double quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
open PolynomialLaurent.Relative
local notation "p" => NatTrans.op plus
local notation "m" => NatTrans.op minus
local notation "L" => laurentFunctor.op

private theorem polynomial_quasiSeparated (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    QuasiSeparatedSpace (polynomialFunctor.op.obj X).unop.obj :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (toIntegerBase X.unop.obj)
      (PolynomialLaurent.polynomialProjection integerRing))

private theorem laurent_quasiSeparated (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    QuasiSeparatedSpace ((L).obj X).unop.obj :=
  quasiSeparatedSpace_of_quasiSeparated
    (pullback.fst (toIntegerBase X.unop.obj)
      (PolynomialLaurent.laurentProjection integerRing))

attribute [local instance] polynomial_quasiSeparated laurent_quasiSeparated

/-- Four genuine QCQS chart components make the twice-contracted native comparison invertible. -/
theorem doubleForwardQuotient_doubleMap_isIso (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    IsIso ((contractionMap p m (contractionMap p m doubleForwardQuotient)).app X) :=
  isIso_doubleContractionMap_app p m doubleForwardQuotient X

/-- The actual variable swap is minus identity on the original fixed K-zero double quotient. -/
theorem doubleContractionSwap_KZero_eq_neg_id (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    doubleContractionSwap (quasiCompactKFunctor 0) X = -𝟙 _ := by
  have h₂ := doubleContractionSwap_neg_contraction_contraction_app
    (quasiCompactKFunctor 2) X
    (doubleContractionSwap_KTwo_eq_neg_id ((L).obj ((L).obj X)))
  have := doubleForwardQuotient_doubleMap_isIso X
  apply (cancel_mono
    ((contractionMap p m (contractionMap p m doubleForwardQuotient)).app X)).1
  rw [← doubleContractionSwap_groupMap doubleForwardQuotient X, h₂]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.comp_id, Category.id_comp]

end Quillen.PerfectComplexes.CoefficientDoubleNativeUnit
