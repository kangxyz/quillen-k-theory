/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawInputForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetRoutes

/-! # The original tensor input square through four actual support inclusions

The geometric input square and the two actual tensor-unitor route squares give the complete
raw tensor input-forgetting square. Both two-edge forgetful routes and all their original
associators remain in the statement; the proof is whole-isomorphism conjugation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex SupportedTensorEvaluation

private theorem conjugateRectangle {E : Type*} [Category* E]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : E}
    {Up : X₀ ≅ X₁} {Uq : X₃ ≅ X₂} {R : X₁ ≅ X₂}
    {LP : X₁ ≅ Y₁} {RP : X₂ ≅ Y₂} {LT : X₀ ≅ Y₀} {RT : X₃ ≅ Y₃}
    {Vp : Y₀ ≅ Y₁} {Vq : Y₃ ≅ Y₂} {S : Y₁ ≅ Y₂}
    (hL : Up ≪≫ LP = LT ≪≫ Vp) (hR : Uq ≪≫ RP = RT ≪≫ Vq)
    (h : R ≪≫ RP = LP ≪≫ S) :
    (Up ≪≫ R ≪≫ Uq.symm) ≪≫ RT = LT ≪≫ (Vp ≪≫ S ≪≫ Vq.symm) := by
  have hR' : Uq.symm ≪≫ RT = RP ≪≫ Vq.symm := by
    calc
      Uq.symm ≪≫ RT = (Uq.symm ≪≫ (RT ≪≫ Vq)) ≪≫ Vq.symm := by
        simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
      _ = (Uq.symm ≪≫ (Uq ≪≫ RP)) ≪≫ Vq.symm := by rw [← hR]
      _ = RP ≪≫ Vq.symm := by rw [Iso.symm_self_id_assoc]
  calc
    (Up ≪≫ R ≪≫ Uq.symm) ≪≫ RT = Up ≪≫ R ≪≫ (Uq.symm ≪≫ RT) := by
      simp only [Iso.trans_assoc]
    _ = Up ≪≫ R ≪≫ (RP ≪≫ Vq.symm) := by rw [hR']
    _ = (Up ≪≫ (R ≪≫ RP)) ≪≫ Vq.symm := by simp only [Iso.trans_assoc]
    _ = (Up ≪≫ (LP ≪≫ S)) ≪≫ Vq.symm := by rw [h]
    _ = ((Up ≪≫ LP) ≪≫ S) ≪≫ Vq.symm := by simp only [Iso.trans_assoc]
    _ = ((LT ≪≫ Vp) ≪≫ S) ≪≫ Vq.symm := by rw [hL]
    _ = LT ≪≫ (Vp ≪≫ S ≪≫ Vq.symm) := by simp only [Iso.trans_assoc]

/-- The full original raw tensor input square retains all four actual support-forgetting edges.
-/
theorem tensorSupportedRawInputForgetSquare {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) :
    isoWhiskerRight (tensorSupportedRawInputIso p q a b h)
        (tensorCoefficientSupportedForget C.obj.hom) ≪≫
        tensorSupportedRawInputForgetRightRoute q b =
      tensorSupportedRawInputForgetLeftRoute p a ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
          (tensorUnitRawInputIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  rw [tensorSupportedRawInputIso_conjugatePullback, tensorUnitRawInputIso_conjugatePullback]
  simp only [isoWhiskerRight_trans, isoWhiskerLeft_trans,
    ← isoWhiskerLeft_symm, ← isoWhiskerRight_symm]
  exact conjugateRectangle (tensorSupportedRawInputForgetLeftRoute_unitor p a)
    (tensorSupportedRawInputForgetRightRoute_unitor q b)
    (supportedPullbackInputForgetSquare p q a b h)

end Quillen.PerfectComplexes
