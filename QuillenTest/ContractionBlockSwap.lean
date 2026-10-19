/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeContractionBlockSwap

/-! Regression laws for actual block transport and repeated sign propagation. -/
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart
universe u w
namespace QuillenTest.ContractionBlockSwap

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)
local notation "L" => laurentFunctor.op

/-- The literal transformed representative returns to its original class under inverse transport. -/
theorem original_representative_recovered
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map (fourfoldLaurentBlockSwap X) ≫ fourfoldContractionπ F X ≫
        (fourfoldContractionBlockSwapNatIso F).inv.app X = fourfoldContractionπ F X := by
  rw [← Category.assoc, ← fourfoldContractionπ_blockSwap, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- Repeated actual transport propagates a sign from one Laurent base through four contractions. -/
theorem sixfold_swap_neg_at
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F ((L).obj ((L).obj ((L).obj ((L).obj X)))) =
      -𝟙 ((C (C F)).obj ((L).obj ((L).obj ((L).obj ((L).obj X)))))) :
    doubleContractionSwap (C (C (C (C F)))) X =
      -𝟙 ((C (C (C (C (C (C F)))))).obj X) := by
  apply doubleContractionSwap_neg_contraction_contraction_app (C (C F)) X
  exact doubleContractionSwap_neg_contraction_contraction_app F ((L).obj ((L).obj X)) h

/-- Pointwise cubic-braid transport also propagates an odd number of contraction steps. -/
theorem fivefold_swap_neg_at
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F ((L).obj ((L).obj ((L).obj X))) =
      -𝟙 ((C (C F)).obj ((L).obj ((L).obj ((L).obj X))))) :
    doubleContractionSwap (C (C (C F))) X = -𝟙 ((C (C (C (C (C F))))).obj X) := by
  apply doubleContractionSwap_neg_contraction_app (C (C F)) X
  apply doubleContractionSwap_neg_contraction_app (C F) ((L).obj X)
  exact doubleContractionSwap_neg_contraction_app F ((L).obj ((L).obj X)) h

end QuillenTest.ContractionBlockSwap
