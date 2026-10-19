/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.SchemeDoubleContractionSwap

/-! Client laws for original double-quotient descent and actual variable-swap transport. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open Quillen.Bass.TwoChart
universe u v w

namespace QuillenTest.DoubleContractionSwap

variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- Successive cokernel descent commutes with an arbitrary target homomorphism. -/
theorem descent_postcomp (F : D ⥤ AddCommGrpCat.{v}) (X : D)
    {A B : AddCommGrpCat.{v}} (f : F.obj (L.obj (L.obj X)) ⟶ A) (g : A ⟶ B)
    (hip : F.map (p.app (L.obj X)) ≫ f = 0)
    (him : F.map (m.app (L.obj X)) ≫ f = 0)
    (hop : F.map (L.map (p.app X)) ≫ f = 0)
    (hom : F.map (L.map (m.app X)) ≫ f = 0) :
    doubleContractionDesc p m F X (f ≫ g)
        (by simp only [← Category.assoc, hip, zero_comp])
        (by simp only [← Category.assoc, him, zero_comp])
        (by simp only [← Category.assoc, hop, zero_comp])
        (by simp only [← Category.assoc, hom, zero_comp]) =
      doubleContractionDesc p m F X f hip him hop hom ≫ g := by
  apply doubleContraction_hom_ext p m F X
  simp only [doubleContractionπ_desc, doubleContractionπ_desc_assoc]

/-- Changing the group-valued model by an actual natural isomorphism retains the original swap. -/
theorem swap_transport_iso
    {F G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{v}} (e : F ≅ G)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op plus) (NatTrans.op minus)
        (contractionMap (NatTrans.op plus) (NatTrans.op minus) e.hom)).app X ≫
        doubleContractionSwap G X ≫
          (contractionMap (NatTrans.op plus) (NatTrans.op minus)
            (contractionMap (NatTrans.op plus) (NatTrans.op minus) e.inv)).app X =
      doubleContractionSwap F X := by
  rw [← Category.assoc, doubleContractionSwap_groupMap, Category.assoc,
    ← NatTrans.comp_app, ← contractionMap_comp, ← contractionMap_comp,
    e.hom_inv_id, contractionMap_id, contractionMap_id]
  simp only [NatTrans.id_app, Category.comp_id]

end QuillenTest.DoubleContractionSwap
