/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeDoubleContractionProductTransport

/-! Regression laws for original representatives and iterated fixed-factor sign transport. -/
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart
universe u w
namespace QuillenTest.DoubleContractionProductTransport

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)
local notation "Q₂" => doubleContractionπ (NatTrans.op plus) (NatTrans.op minus)

/-- Inverse transport recovers the unchanged class from the two literal interchanges. -/
theorem original_representative_recovered
    {S : Scheme.{u}} (q : S ⟶ integerBase) [QuasiCompact q]
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map (productDoubleLaurentOppositeMap q X) ≫
        Q₂ F ((qcBaseProductFunctor q).op.obj X) ≫
          (productDoubleContractionTransportIso q F).inv.app X =
      Q₂ ((qcBaseProductFunctor q).op ⋙ F) X := by
  rw [← Category.assoc, ← productDoubleContractionTransportIso_π, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- Two fixed factors require a sign only at the single resulting product base. -/
theorem two_factor_swap_neg_at
    {S T : Scheme.{u}} (q : S ⟶ integerBase) (r : T ⟶ integerBase)
    [QuasiCompact q] [QuasiCompact r]
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F
        ((qcBaseProductFunctor q).op.obj ((qcBaseProductFunctor r).op.obj X)) =
      -𝟙 ((C (C F)).obj
        ((qcBaseProductFunctor q).op.obj ((qcBaseProductFunctor r).op.obj X)))) :
    doubleContractionSwap
        ((qcBaseProductFunctor r).op ⋙ (qcBaseProductFunctor q).op ⋙ F) X =
      -𝟙 ((C (C ((qcBaseProductFunctor r).op ⋙ (qcBaseProductFunctor q).op ⋙ F))).obj X) := by
  apply doubleContractionSwap_neg_product_app r ((qcBaseProductFunctor q).op ⋙ F) X
  exact doubleContractionSwap_neg_product_app q F ((qcBaseProductFunctor r).op.obj X) h

end QuillenTest.DoubleContractionProductTransport
