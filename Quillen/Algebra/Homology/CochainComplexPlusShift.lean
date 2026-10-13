/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Algebra.Homology.CochainComplexPlusNatTrans
public import Quillen.Algebra.Homology.CochainComplexPlusFunctoriality
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Original bounded-below complex maps and quasi-isomorphisms under shifts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  {F G : A ⥤ B} [F.Additive] [G.Additive]
/-- The original componentwise transformation retains the installed shifts. -/
instance NatTrans.mapCochainComplexPlusCommShift (α : F ⟶ G) :
    NatTrans.CommShift (NatTrans.mapCochainComplexPlus α) ℤ := by
  apply NatTrans.CommShift.of_comp_faithful (G := CochainComplex.Plus.ι B) (h := ?_)
  have he : Functor.whiskerRight (NatTrans.mapCochainComplexPlus α)
      (CochainComplex.Plus.ι B) = F.mapCochainComplexPlusCompι.hom ≫
      Functor.whiskerLeft (CochainComplex.Plus.ι A)
        (NatTrans.mapHomologicalComplex α (.up ℤ)) ≫ G.mapCochainComplexPlusCompι.inv := by
    ext K : 2
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.whiskerRight_app,
      ObjectProperty.ι_map, NatTrans.comp_app, Functor.mapCochainComplexPlusCompι_hom_app,
      Functor.whiskerLeft_app, Functor.mapCochainComplexPlusCompι_inv_app, Category.id_comp]
    symm
    apply Category.comp_id
  rw [he]
  infer_instance
/-- The literal componentwise composition comparison retains the installed shifts. -/
instance Functor.mapCochainComplexPlusCompIsoCommShift
    {C : Type*} [Category* C] [Preadditive C] (F : A ⥤ B) [F.Additive]
    (G : B ⥤ C) [G.Additive] :
    NatTrans.CommShift (Functor.mapCochainComplexPlusCompIso F G).hom ℤ := by
  apply NatTrans.CommShift.of_comp_faithful (G := CochainComplex.Plus.ι C) (h := ?_)
  let e := Functor.associator F.mapCochainComplexPlus G.mapCochainComplexPlus
      (CochainComplex.Plus.ι C) ≪≫
    isoWhiskerLeft F.mapCochainComplexPlus G.mapCochainComplexPlusCompι ≪≫
    (Functor.associator F.mapCochainComplexPlus (CochainComplex.Plus.ι B)
      (G.mapHomologicalComplex (.up ℤ))).symm ≪≫
    isoWhiskerRight F.mapCochainComplexPlusCompι (G.mapHomologicalComplex (.up ℤ)) ≪≫
    Functor.associator (CochainComplex.Plus.ι A) (F.mapHomologicalComplex (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ))
  have he : Functor.whiskerRight (Functor.mapCochainComplexPlusCompIso F G).hom
      (CochainComplex.Plus.ι C) = (F ⋙ G).mapCochainComplexPlusCompι.hom ≫
      Functor.whiskerLeft (CochainComplex.Plus.ι A)
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv ≫ e.inv := by
    ext K : 2
    simp [e, Functor.mapCochainComplexPlusCompIso, Functor.mapCochainComplexPlusCompι]
    rfl
  rw [he]
  have : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Iso.symm_hom]
    infer_instance
  infer_instance
end CategoryTheory
namespace CochainComplex.Plus
/-- The original bounded-below quasi-isomorphisms are stable under installed shifts. -/
instance quasiIsoCompatibleWithShift (C : Type*) [Category* C]
    [Preadditive C] [CategoryWithHomology C] :
    (quasiIso C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L g
    change HomologicalComplex.quasiIso C (.up ℤ) ((g⟦n⟧').hom) ↔
      HomologicalComplex.quasiIso C (.up ℤ) g.hom
    rw [← MorphismProperty.IsCompatibleWithShift.iff
      (HomologicalComplex.quasiIso C (.up ℤ)) g.hom n]
    exact (HomologicalComplex.quasiIso C (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι C).commShiftIso n) (Arrow.mk g))
end CochainComplex.Plus
