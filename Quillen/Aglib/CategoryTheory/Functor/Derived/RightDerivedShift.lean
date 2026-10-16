/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-! # Shift compatibility detected by an original right-derived unit -/

@[expose] public section
noncomputable section
open CategoryTheory
namespace CategoryTheory.Functor
variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (RF : H ⥤ D) {F : C ⥤ D} {L : C ⥤ H}
  (α : F ⟶ L ⋙ RF) (W : MorphismProperty C) [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
  [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A] [RF.CommShift A]
  [NatTrans.CommShift α A]
  (G : H ⥤ D) [G.CommShift A] (γ : RF ⟶ G)
  [NatTrans.CommShift (α ≫ whiskerLeft L γ) A]
include α W in
/-- Compatibility after the original right-derived unit detects compatibility with shifts. -/
theorem commShift_of_rightDerivedUnit : NatTrans.CommShift γ A where
  shift_comm a := by
    apply rightDerived_ext _ (IsRightDerivedFunctor.precomposeShiftNatTrans RF α a) W
    ext X
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      IsRightDerivedFunctor.precomposeShiftNatTrans_app, Category.assoc]
    rw [γ.naturality_assoc]
    have hα := NatTrans.shift_app_comm α a X
    have hβ := NatTrans.shift_app_comm (α ≫ whiskerLeft L γ) a X
    simp only [commShiftIso_comp_hom_app, NatTrans.comp_app, whiskerLeft_app,
      Category.assoc] at hα hβ
    rw [← reassoc_of% hα]
    simpa only [Functor.map_comp, Category.assoc] using hβ

omit [NatTrans.CommShift (α ≫ whiskerLeft L γ) A] in
/-- A shift-compatible original factorization induces a shift-compatible derived map. -/
theorem commShift_rightDerivedDesc (β : F ⟶ L ⋙ G) [NatTrans.CommShift β A] :
    NatTrans.CommShift (RF.rightDerivedDesc α W G β) A := by
  have : NatTrans.CommShift (α ≫ whiskerLeft L (RF.rightDerivedDesc α W G β)) A := by
    rw [rightDerived_fac]
    infer_instance
  exact commShift_of_rightDerivedUnit RF α W A G _
end CategoryTheory.Functor
