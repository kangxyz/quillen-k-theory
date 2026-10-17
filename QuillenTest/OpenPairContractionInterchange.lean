/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.OpenPairContractionMiddle

/-! # Original open-pair quotient representatives under inverse product interchange -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.Bass
open Quillen.Bass.TwoChart
universe u w

/-- Inverse product transport recovers the original quotient representative on both pair entries.
-/
example {S : AlgebraicGeometry.Scheme.{u}} (q : S ⟶ integerBase) [QuasiCompact q]
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (F.map ((pairProductLaurentOppositeIso q).hom.app X) ≫
      (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
        ((pairBaseProductFunctor q).op.obj X)) ≫
      (pairProductContractionTransportIso q F).inv.app X =
    (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      ((pairBaseProductFunctor q).op ⋙ F)).app X := by
  rw [← pairProductContractionTransportIso_π q F X, Category.assoc,
    Iso.hom_inv_id_app, Category.comp_id]

/-- Interchange leaves the original common-corner group unchanged. -/
example (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (pairContractionBassMiddleIso F).hom.τ₁ = 𝟙 _ := rfl
