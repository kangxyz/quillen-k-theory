/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeAffineDoubleContractionSign
public import Quillen.KTheory.Bass.SchemeContractionBlockSwap

/-! Regression laws for affine parameter transport and literal Laurent-family propagation. -/
public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart
universe u w
namespace QuillenTest.AffineDoubleContractionSign

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)

/-- The actual sign is invariant in both directions under an original parameter isomorphism. -/
theorem parameter_sign_iff
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (e : X ≅ Y) :
    doubleContractionSwap F X = -𝟙 ((C (C F)).obj X) ↔
      doubleContractionSwap F Y = -𝟙 ((C (C F)).obj Y) :=
  ⟨doubleContractionSwap_neg_of_iso F e.symm, doubleContractionSwap_neg_of_iso F e⟩

/-- A Spec-only sign propagates through the literal four-variable block on an affine parameter. -/
theorem affine_fourfold_sign_of_under_spec
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (h : ∀ a : Under integerRing,
      doubleContractionSwap F (Scheme.Bass.affineSchemeFunctor.obj a.right) = -𝟙 _)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) [IsAffine X.unop.obj] :
    doubleContractionSwap (C (C F)) X = -𝟙 ((C (C (C (C F)))).obj X) := by
  let := isAffine_laurent_parameter X inferInstance
  let := isAffine_laurent_parameter (laurentFunctor.op.obj X) inferInstance
  apply doubleContractionSwap_neg_contraction_contraction_app F X
  exact doubleContractionSwap_neg_affine_of_under_spec F h
    (laurentFunctor.op.obj (laurentFunctor.op.obj X))

end QuillenTest.AffineDoubleContractionSign
